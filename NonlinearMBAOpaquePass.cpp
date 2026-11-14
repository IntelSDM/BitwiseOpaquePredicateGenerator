#include "NonlinearMBAOpaquePass.h"

#include "mbagen/AuxSource.h"
#include "mbagen/FoldBarrier.h"
#include "mbagen/IdentityGenerator.h"
#include "mbagen/MBABasis.h"
#include "mbagen/NonlinearOpaqueEq.h"
#include "mbagen/NonlinearOpaqueFamily.h"

#include "llvm/ADT/ArrayRef.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/DenseSet.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/ADT/StringRef.h"
#include "llvm/Analysis/DomTreeUpdater.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/CFG.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/Dominators.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/GlobalVariable.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/InstrTypes.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/MDBuilder.h"
#include "llvm/IR/Metadata.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/PassManager.h"
#include "llvm/IR/Value.h"
#include "llvm/IR/Verifier.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"

#include <algorithm>
#include <chrono>
#include <cstdint>
#include <cstring>
#include <random>
#include <string>
#include <vector>

using namespace llvm;

llvm::cl::opt<bool> NonlinearMBAOpaqueEnable("obfnlmbaopq", llvm::cl::init(true), llvm::cl::desc("Nonlinear MBA opaque predicate pass."));

static constexpr unsigned Density = 100;
static constexpr unsigned PerFunctionCap = 120;
static constexpr unsigned MinBBInsts = 1;
static constexpr bool SkipLoops = true;
static constexpr bool SkipEntryBB = true;
static constexpr unsigned CrossWidthPct = 0;
static constexpr unsigned IdentityV = 3;
static constexpr unsigned IdentityGroupCount = 3;
static constexpr unsigned IdentityVerifySamples = 100;
static constexpr unsigned IdentityMaxRetries = 6;
static constexpr unsigned IdentityTierFlag = 8;
static constexpr unsigned BarrierPoolSize = 16;
static constexpr unsigned BarrierWeightLegacy = 0;
static constexpr unsigned BarrierWeightXor = 50;
static constexpr unsigned BarrierWeightAdd = 25;
static constexpr unsigned BarrierWeightSub = 25;

static constexpr unsigned DiamondMinSuffix = 2;
static constexpr unsigned LoopMinLimit = 4;
static constexpr unsigned LoopMaxLimit = 10;

static constexpr unsigned LoopModeWeight = 20;
static constexpr unsigned LoopClassicModeWeight = 20;
static constexpr unsigned DiamondModeWeight = 40;

static constexpr unsigned SampledDecoyPct = 70;
static constexpr unsigned SampledMinInsts = 3;
static constexpr unsigned SampledMaxInsts = 10;

static constexpr unsigned OuterWrapMinDepth = 2;
static constexpr unsigned OuterWrapMaxDepth = 7;

static constexpr unsigned BogusSinkPoolSize = 8;
static constexpr unsigned BogusMinOps = 3;
static constexpr unsigned BogusMaxOps = 11;
static constexpr unsigned BogusMaxExtraSinkLoads = 3;
static constexpr unsigned BogusMultiStoreChancePct = 25;

static constexpr unsigned CmpTreeDepthMin = 2;
static constexpr unsigned CmpTreeDepthMax = 4;
static constexpr unsigned EnsembleModePct = 40;
static constexpr unsigned EnsembleNSubTreesMin = 2;
static constexpr unsigned EnsembleNSubTreesMax = 4;
static constexpr unsigned EnsembleSubDepth = 2;

static constexpr unsigned ConstPerturbationPct = 60;
static constexpr unsigned ConstPerturbationDepth = 2;

static constexpr const char* DoneMDKind = "nlmbaopq.done";

static constexpr uint64_t FNV1a64(const char* s)
{
    uint64_t h = 0xcbf29ce484222325ULL;
    while (*s)
    {
        h ^= (uint8_t)(*s);
        h *= 0x100000001b3ULL;
        ++s;
    }
    return h;
}

static uint64_t FNV1a64Range(llvm::StringRef s)
{
    uint64_t h = 0xcbf29ce484222325ULL;
    for (char c : s)
    {
        h ^= (uint8_t)c;
        h *= 0x100000001b3ULL;
    }
    return h;
}

static bool HasAnnotationTag(Function& f, const char* tag)
{
    Module* m = f.getParent();
    GlobalVariable* ga = m->getGlobalVariable("llvm.global.annotations");
    if (!ga || !ga->hasInitializer()) return false;
    auto* ca = dyn_cast<ConstantArray>(ga->getOperand(0));
    if (!ca) return false;
    for (unsigned i = 0; i < ca->getNumOperands(); ++i)
    {
        auto* cs = dyn_cast<ConstantStruct>(ca->getOperand(i));
        if (!cs || cs->getNumOperands() < 2) continue;
        if (cs->getOperand(0)->stripPointerCasts() != &f) continue;
        auto* annogv = dyn_cast<GlobalVariable>(cs->getOperand(1)->stripPointerCasts());
        if (!annogv || !annogv->hasInitializer()) continue;
        auto* cds = dyn_cast<ConstantDataSequential>(annogv->getInitializer());
        if (!cds || !cds->isString()) continue;
        if (strcmp(cds->getAsString().str().c_str(), tag) == 0) return true;
    }
    return false;
}

static bool HasObfuscateAnnotation(Function& f) { return HasAnnotationTag(f, "obfus"); }
static bool HasNoObfuscateAnnotation(Function& f) { return HasAnnotationTag(f, "noobfus"); }
static bool HasNoMBAAnnotation(Function& f) { return HasAnnotationTag(f, "nomba"); }
static bool HasNoOpaqueAnnotation(Function& f) { return HasAnnotationTag(f, "noopaque"); }

static std::mt19937_64 Rng;
static mbagen::ModuleBarrierState BarrierState;

static mbagen::Tier TierFromFlag(unsigned t)
{
    switch (t)
    {
        case 6: return mbagen::Tier::T6;
        case 7: return mbagen::Tier::T7;
        case 8:
        default: return mbagen::Tier::T8;
    }
}

static bool DensityGateOpen(const Function& f, size_t siteidx)
{
    if (Density >= 100u) return true;
    if (Density == 0u) return false;
    uint64_t x = FNV1a64Range(f.getName());
    x ^= (uint64_t)siteidx * 0x9E3779B97F4A7C15ULL;
    x ^= 0x4E4C4F504151554EULL;
    x ^= x >> 30;
    x *= 0xBF58476D1CE4E5B9ULL;
    x ^= x >> 27;
    x *= 0x94D049BB133111EBULL;
    x ^= x >> 31;
    const uint32_t roll = (uint32_t)(x & 0xFFu);
    const uint32_t thr = (Density * 256u) / 100u;
    return roll < thr;
}

static bool IsEligibleInsertionPoint(Instruction& i)
{
    if (isa<PHINode>(&i)) return false;
    if (i.isTerminator()) return false;
    if (isa<LandingPadInst>(&i)) return false;
    if (isa<CatchPadInst>(&i)) return false;
    if (isa<CleanupPadInst>(&i)) return false;
    if (isa<AllocaInst>(&i)) return false;
    return true;
}

static Instruction* PickRandomEligibleInBB(BasicBlock& bb, std::mt19937_64& rng)
{
    SmallVector<Instruction*, 32> eligible;
    BasicBlock::iterator it = bb.getFirstInsertionPt();
    if (it == bb.end()) return nullptr;
    for (; it != bb.end(); ++it)
    {
        if (IsEligibleInsertionPoint(*it)) eligible.push_back(&*it);
    }
    if (eligible.empty()) return nullptr;
    return eligible[(size_t)(rng() % eligible.size())];
}

static unsigned CountInsts(const BasicBlock& bb)
{
    unsigned c = 0;
    for (auto it = bb.begin(); it != bb.end(); ++it) ++c;
    return c;
}

static bool BBAlreadyProcessed(BasicBlock& bb)
{
    Instruction* term = bb.getTerminator();
    if (!term) return false;
    return term->getMetadata(DoneMDKind) != nullptr;
}

static void MarkBBProcessed(BasicBlock& bb)
{
    Instruction* term = bb.getTerminator();
    if (!term) return;
    LLVMContext& c = bb.getContext();
    term->setMetadata(DoneMDKind, MDNode::get(c, {}));
}

static bool IsOurBBName(StringRef n)
{
    return n.starts_with(".NLMBAOpaque") || n.starts_with("NLMBAOpaque");
}

static BasicBlock* PickNextBB(Function& f)
{
    BasicBlock* entrybb = &f.getEntryBlock();
    for (BasicBlock& bb : f)
    {
        if (bb.isEHPad()) continue;
        if (SkipEntryBB && &bb == entrybb) continue;
        if (BBAlreadyProcessed(bb)) continue;
        if (IsOurBBName(bb.getName())) continue;
        if (CountInsts(bb) < MinBBInsts) continue;
        bool anyeligible = false;
        for (Instruction& i : bb)
        {
            if (IsEligibleInsertionPoint(i))
            {
                anyeligible = true;
                break;
            }
        }
        if (!anyeligible) continue;
        return &bb;
    }
    return nullptr;
}

static bool IsSafeInstructionToClone(const Instruction& i)
{
    if (isa<PHINode>(&i)) return false;
    if (i.isTerminator()) return false;
    if (isa<AllocaInst>(&i)) return false;
    if (isa<LandingPadInst>(&i)) return false;
    if (isa<CatchPadInst>(&i)) return false;
    if (isa<CleanupPadInst>(&i)) return false;
    if (isa<VAArgInst>(&i)) return false;
    if (isa<FenceInst>(&i)) return false;
    if (isa<AtomicRMWInst>(&i)) return false;
    if (isa<AtomicCmpXchgInst>(&i)) return false;
    if (isa<CallBase>(&i)) return false;
    if (auto* li = dyn_cast<LoadInst>(&i))
    {
        if (li->isVolatile() || li->isAtomic()) return false;
        return true;
    }
    if (auto* si = dyn_cast<StoreInst>(&i))
    {
        if (si->isVolatile() || si->isAtomic()) return false;
        return true;
    }
    if (isa<BinaryOperator>(&i)) return true;
    if (isa<UnaryOperator>(&i)) return true;
    if (isa<CastInst>(&i)) return true;
    if (isa<GetElementPtrInst>(&i)) return true;
    if (isa<ICmpInst>(&i)) return true;
    if (isa<FCmpInst>(&i)) return true;
    if (isa<SelectInst>(&i)) return true;
    if (isa<ExtractValueInst>(&i)) return true;
    if (isa<InsertValueInst>(&i)) return true;
    return false;
}

static void BuildStackSlotRemap(Function& f, ArrayRef<Instruction*> sampled, std::mt19937_64& rng, DenseMap<AllocaInst*, Value*>& outremap)
{
    SmallVector<AllocaInst*, 16> allallocas;
    for (BasicBlock& bb : f)
    {
        for (Instruction& i : bb)
        {
            if (auto* a = dyn_cast<AllocaInst>(&i)) allallocas.push_back(a);
        }
    }

    DenseMap<Type*, SmallVector<AllocaInst*, 4>> bytype;
    for (AllocaInst* a : allallocas) bytype[a->getAllocatedType()].push_back(a);

    DenseSet<AllocaInst*> referenced;
    for (Instruction* i : sampled)
    {
        for (Use& u : i->operands())
        {
            if (auto* a = dyn_cast<AllocaInst>(u.get())) referenced.insert(a);
        }
    }

    for (AllocaInst* src : referenced)
    {
        auto it = bytype.find(src->getAllocatedType());
        if (it == bytype.end()) { outremap[src] = src; continue; }
        SmallVector<AllocaInst*, 4>& group = it->second;
        if (group.size() < 2) { outremap[src] = src; continue; }
        AllocaInst* pick = nullptr;
        for (int tries = 0; tries < 8 && !pick; ++tries)
        {
            AllocaInst* cand = group[(size_t)(rng() % group.size())];
            if (cand != src) pick = cand;
        }
        outremap[src] = pick ? (Value*)pick : (Value*)src;
    }
}

static Value* ApplyIdentityPreservingWrap(IRBuilder<>& b, Value* lhs, IntegerType* ity, mbagen::ModuleBarrierState& bs, std::mt19937_64& rng, unsigned depth)
{
    for (unsigned i = 0; i < depth; ++i)
    {
        const unsigned kind = (unsigned)(rng() % 5u);
        const uint64_t k = (uint64_t)rng() | 1ull;
        Value* kval = mbagen::InsertFoldBarrier(b, ConstantInt::get(ity, k), bs);

        switch (kind)
        {
            case 0:
            {
                Value* t = b.CreateAdd(lhs, kval, "OwAdd");
                lhs = b.CreateSub(t, kval, "OwSub");
                break;
            }
            case 1:
            {
                Value* notk = b.CreateNot(kval, "OwNotK");
                Value* a = b.CreateAnd(lhs, kval, "OwAndK");
                Value* bpart = b.CreateAnd(lhs, notk, "OwAndNotK");
                lhs = b.CreateAdd(a, bpart, "OwSum");
                break;
            }
            case 2:
            {
                Value* t = b.CreateOr(lhs, kval, "OwOr");
                lhs = b.CreateXor(t, kval, "OwXor");
                break;
            }
            case 3:
            {
                lhs = b.CreateMul(lhs, kval, "OwMul");
                break;
            }
            case 4:
            default:
            {
                Value* a = b.CreateAnd(lhs, kval, "OwAnd");
                lhs = b.CreateXor(lhs, a, "OwXorPart");
                break;
            }
        }
    }
    return lhs;
}

static Value* EmitCompareRecipe(IRBuilder<>& b, Value* lhs, IntegerType* ity, mbagen::ModuleBarrierState& bs, std::mt19937_64& rng, bool& outalwaystrue)
{
    if ((unsigned)(rng() % 100u) < EnsembleModePct)
    {
        const unsigned nspan = EnsembleNSubTreesMax - EnsembleNSubTreesMin + 1u;
        const unsigned n = EnsembleNSubTreesMin + (unsigned)(rng() % nspan);
        return mbagen::EmitSynthesizedCompareEnsemble(b, lhs, ity, bs, rng, outalwaystrue, n, EnsembleSubDepth, true);
    }
    const unsigned depthspan = CmpTreeDepthMax - CmpTreeDepthMin + 1u;
    const unsigned depth = CmpTreeDepthMin + (unsigned)(rng() % depthspan);
    return mbagen::EmitSynthesizedCompare(b, lhs, ity, bs, rng, outalwaystrue, depth, true);
}

static bool FindMovableSuffix(BasicBlock& bb, SmallVectorImpl<Instruction*>& out)
{
    out.clear();
    Instruction* term = bb.getTerminator();
    if (!term) return false;
    DenseSet<Instruction*> inwin;
    for (Instruction* curr = term->getPrevNode(); curr; curr = curr->getPrevNode())
    {
        if (isa<PHINode>(curr) || isa<AllocaInst>(curr)) break;
        if (!IsSafeInstructionToClone(*curr)) break;
        bool ok = true;
        for (User* u : curr->users())
        {
            Instruction* ui = dyn_cast<Instruction>(u);
            if (!ui || !inwin.contains(ui)) { ok = false; break; }
        }
        if (!ok) break;
        out.push_back(curr);
        inwin.insert(curr);
    }
    std::reverse(out.begin(), out.end());
    return !out.empty();
}

static void TruncateSuffixRandomly(SmallVectorImpl<Instruction*>& suffix, std::mt19937_64& rng)
{
    if (suffix.size() <= DiamondMinSuffix) return;
    const unsigned fullsize = (unsigned)suffix.size();
    const unsigned span = fullsize - DiamondMinSuffix + 1u;
    const unsigned keep = DiamondMinSuffix + (unsigned)(rng() % span);
    const unsigned drop = fullsize - keep;
    if (drop > 0) suffix.erase(suffix.begin(), suffix.begin() + drop);
}

static void CloneSuffixWithStackRemap(IRBuilder<>& insertbuilder, ArrayRef<Instruction*> suffix, const DenseMap<AllocaInst*, Value*>& stackremap, mbagen::ModuleBarrierState& bs, std::mt19937_64& rng)
{
    DenseMap<Value*, Value*> valmap;
    for (Instruction* orig : suffix)
    {
        Instruction* cloned = orig->clone();
        cloned->setName(orig->getName() + ".Pollute");
        SmallVector<std::pair<unsigned, MDNode*>, 4> allmd;
        cloned->getAllMetadata(allmd);
        for (auto& p : allmd) cloned->setMetadata(p.first, nullptr);
        for (unsigned opidx = 0; opidx < cloned->getNumOperands(); ++opidx)
        {
            Value* op = cloned->getOperand(opidx);
            if (!op) continue;
            auto vmit = valmap.find(op);
            if (vmit != valmap.end()) { cloned->setOperand(opidx, vmit->second); continue; }
            if (auto* a = dyn_cast<AllocaInst>(op))
            {
                auto rmit = stackremap.find(a);
                if (rmit != stackremap.end() && rmit->second != (Value*)a) cloned->setOperand(opidx, rmit->second);
                continue;
            }

            if (auto* ci = dyn_cast<ConstantInt>(op))
            {
                if (ConstPerturbationPct == 0) continue;
                if (!ci->getType()->isIntegerTy()) continue;
                // GEP index positions, switch cases, and the shift-amount operand of Shl/LShr/AShr require a literal ConstantInt so replacing those operands with a synthesized Value is poison and must be skipped before the perturbation roll
                if (isa<GetElementPtrInst>(cloned)) continue;
                if (isa<SwitchInst>(cloned)) continue;
                const unsigned opc = cloned->getOpcode();
                if ((opc == Instruction::Shl || opc == Instruction::LShr || opc == Instruction::AShr) && opidx == 1u) continue;
                if ((unsigned)(rng() % 100u) >= ConstPerturbationPct) continue;

                IntegerType* ity = cast<IntegerType>(ci->getType());
                Value* synth = mbagen::EmitSynthesizedConstant(insertbuilder, ity, bs, rng, ConstPerturbationDepth);
                cloned->setOperand(opidx, synth);
                continue;
            }
        }
        insertbuilder.Insert(cloned);
        valmap[orig] = cloned;
    }
}

static bool TryEmitDiamond(Function& f, BasicBlock* bb, size_t siteidx, DomTreeUpdater& dtu, LoopInfo& li)
{
    (void)li;
    SmallVector<Instruction*, 16> suffix;
    if (!FindMovableSuffix(*bb, suffix)) return false;
    TruncateSuffixRandomly(suffix, Rng);
    if (suffix.size() < DiamondMinSuffix) return false;

    Instruction* splitpt = suffix.front();
    LLVMContext& c = f.getContext();
    IntegerType* ity = IntegerType::get(c, 64);

    IRBuilder<> predb(splitpt);
    std::vector<Value*> harvested = mbagen::GatherAuxValues(predb, dtu.getDomTree(), ity, IdentityV, Rng, CrossWidthPct);
    if (harvested.size() < 1) return false;
    for (Value* v : harvested)
    {
        if (!v || v->getType() != ity) return false;
    }

    Value* lhs = mbagen::EmitNonlinearOpaqueEquation(predb, harvested, ity, BarrierState, Rng, IdentityV, TierFromFlag(IdentityTierFlag), IdentityGroupCount, IdentityVerifySamples, IdentityMaxRetries);
    if (!lhs || isa<ConstantInt>(lhs)) return false;

    const unsigned depthspan = OuterWrapMaxDepth - OuterWrapMinDepth + 1u;
    const unsigned wrapdepth = OuterWrapMinDepth + (unsigned)(Rng() % depthspan);
    lhs = ApplyIdentityPreservingWrap(predb, lhs, ity, BarrierState, Rng, wrapdepth);

    bool condalwaystrue = false;
    Value* cond = EmitCompareRecipe(predb, lhs, ity, BarrierState, Rng, condalwaystrue);

    BasicBlock* tail = bb->splitBasicBlock(splitpt, bb->getName() + ".NLMBAOpaqueTail");

    // realbb MUST use a bland name without the NLMBAOpaque prefix so PickNextBB keeps considering it a candidate for further opaque chaining; prefixed names are filtered by IsOurBBName and would pin chain depth at 1
    BasicBlock* realbb = BasicBlock::Create(c, "ChainReal." + std::to_string(siteidx), &f, tail);
    BasicBlock* pollutebb = BasicBlock::Create(c, "NLMBAOpaquePollute." + std::to_string(siteidx), &f, tail);

    for (Instruction* inst : suffix)
    {
        inst->removeFromParent();
        inst->insertInto(realbb, realbb->end());
    }
    IRBuilder<> rb(realbb);
    rb.CreateBr(tail);

    DenseMap<AllocaInst*, Value*> remap;
    BuildStackSlotRemap(f, suffix, Rng, remap);
    IRBuilder<> pb(pollutebb);
    CloneSuffixWithStackRemap(pb, suffix, remap, BarrierState, Rng);
    pb.CreateBr(tail);

    Instruction* oldterm = bb->getTerminator();
    oldterm->eraseFromParent();
    IRBuilder<> termb(bb);
    MDBuilder mdb(c);
    BasicBlock* brtruedest = nullptr;
    BasicBlock* brfalsedest = nullptr;
    MDNode* weights = nullptr;
    if (condalwaystrue)
    {
        brtruedest = realbb;
        brfalsedest = pollutebb;
        weights = mdb.createBranchWeights(100000u, 1u);
    }
    else
    {
        brtruedest = pollutebb;
        brfalsedest = realbb;
        weights = mdb.createBranchWeights(1u, 100000u);
    }
    BranchInst* br = termb.CreateCondBr(cond, brtruedest, brfalsedest);
    br->setMetadata(LLVMContext::MD_prof, weights);

    SmallVector<DominatorTree::UpdateType, 8> updates = {
        {DominatorTree::Insert, bb, realbb},
        {DominatorTree::Insert, bb, pollutebb},
        {DominatorTree::Insert, realbb, tail},
        {DominatorTree::Insert, pollutebb, tail},
        {DominatorTree::Delete, bb, tail},
    };
    dtu.applyUpdates(updates);

    MarkBBProcessed(*bb);
    return true;
}

static bool TryEmitLoop(Function& f, BasicBlock* bb, size_t siteidx, DomTreeUpdater& dtu, LoopInfo& li)
{
    (void)li;
    SmallVector<Instruction*, 16> suffix;
    if (!FindMovableSuffix(*bb, suffix)) return false;
    TruncateSuffixRandomly(suffix, Rng);
    if (suffix.size() < DiamondMinSuffix) return false;

    LLVMContext& c = f.getContext();
    IntegerType* ity = IntegerType::get(c, 64);

    Instruction* splitpt = suffix.front();

    IRBuilder<> headb(splitpt);
    std::vector<Value*> harvested = mbagen::GatherAuxValues(headb, dtu.getDomTree(), ity, IdentityV, Rng, CrossWidthPct);
    if (harvested.size() < 1) return false;
    for (Value* v : harvested)
    {
        if (!v || v->getType() != ity) return false;
    }

    const unsigned loopspan = LoopMaxLimit - LoopMinLimit + 1u;
    const uint64_t looplimit = LoopMinLimit + (uint64_t)(Rng() % loopspan);
    Value* limitval = mbagen::InsertFoldBarrier(headb, ConstantInt::get(ity, looplimit), BarrierState);

    BasicBlock* tail = bb->splitBasicBlock(splitpt, bb->getName() + ".NLMBAOpaqueLTail");

    BasicBlock* loopheader = BasicBlock::Create(c, "NLMBAOpaqueLH." + std::to_string(siteidx), &f, tail);
    BasicBlock* loopbody = BasicBlock::Create(c, "NLMBAOpaqueLB." + std::to_string(siteidx), &f, tail);
    // afterloop uses a bland name without the NLMBAOpaque prefix so PickNextBB keeps it eligible for further opaque chaining; prefixed names get filtered out by IsOurBBName
    BasicBlock* afterloop = BasicBlock::Create(c, "ChainAfter." + std::to_string(siteidx), &f, tail);
    BasicBlock* pollute = BasicBlock::Create(c, "NLMBAOpaqueLP." + std::to_string(siteidx), &f, tail);

    Instruction* oldterm = bb->getTerminator();
    oldterm->eraseFromParent();
    IRBuilder<> bbb(bb);
    bbb.CreateBr(loopheader);

    IRBuilder<> lhb(loopheader);
    PHINode* counterphi = lhb.CreatePHI(ity, 2, "Counter");
    PHINode* accumphi = lhb.CreatePHI(ity, 2, "Accum");
    counterphi->addIncoming(ConstantInt::get(ity, 0), bb);
    accumphi->addIncoming(harvested[0], bb);

    SmallVector<Value*, 4> loopinputs;
    loopinputs.push_back(counterphi);
    loopinputs.push_back(accumphi);
    for (size_t i = 1; i < harvested.size() && loopinputs.size() < IdentityV; ++i) loopinputs.push_back(harvested[i]);
    while (loopinputs.size() < IdentityV) loopinputs.push_back(harvested[0]);

    Value* lhs = mbagen::EmitNonlinearOpaqueEquation(lhb, loopinputs, ity, BarrierState, Rng, IdentityV, TierFromFlag(IdentityTierFlag), IdentityGroupCount, IdentityVerifySamples, IdentityMaxRetries);
    if (!lhs || isa<ConstantInt>(lhs))
    {
        // cleanup ordering is load bearing. The phis must be erased before bb is repointed away from loopheader so the phi's incoming-from-bb use doesn't dangle, and loopheader must lose its predecessor before eraseFromParent runs because debug builds assert on live predecessor BB erase
        counterphi->eraseFromParent();
        accumphi->eraseFromParent();
        bb->getTerminator()->eraseFromParent();
        IRBuilder<> restoreb(bb);
        restoreb.CreateBr(tail);
        loopheader->eraseFromParent();
        loopbody->eraseFromParent();
        afterloop->eraseFromParent();
        pollute->eraseFromParent();
        return false;
    }

    const unsigned depthspan = OuterWrapMaxDepth - OuterWrapMinDepth + 1u;
    const unsigned wrapdepth = OuterWrapMinDepth + (unsigned)(Rng() % depthspan);
    lhs = ApplyIdentityPreservingWrap(lhb, lhs, ity, BarrierState, Rng, wrapdepth);

    bool condalwaystrue = false;
    Value* condok = EmitCompareRecipe(lhb, lhs, ity, BarrierState, Rng, condalwaystrue);

    MDBuilder mdb(c);
    BasicBlock* okdest = nullptr;
    BasicBlock* faildest = nullptr;
    MDNode* okweights = nullptr;
    if (condalwaystrue)
    {
        okdest = loopbody;
        faildest = pollute;
        okweights = mdb.createBranchWeights(100000u, 1u);
    }
    else
    {
        okdest = pollute;
        faildest = loopbody;
        okweights = mdb.createBranchWeights(1u, 100000u);
    }
    BranchInst* lhbr = lhb.CreateCondBr(condok, okdest, faildest);
    lhbr->setMetadata(LLVMContext::MD_prof, okweights);

    IRBuilder<> lbb(loopbody);
    Value* counternext = lbb.CreateAdd(counterphi, ConstantInt::get(ity, 1), "CounterNext");
    const uint64_t accumk = (uint64_t)Rng() | 1ull;
    Value* accummul = lbb.CreateMul(counterphi, ConstantInt::get(ity, accumk), "AccumMul");
    Value* accumnext = lbb.CreateXor(accumphi, accummul, "AccumNext");
    Value* exitcond = lbb.CreateICmpULT(counternext, limitval, "ExitCond");

    MDNode* loopweights = mdb.createBranchWeights(100000u, 1u);
    BranchInst* lbbr = lbb.CreateCondBr(exitcond, loopheader, afterloop);
    lbbr->setMetadata(LLVMContext::MD_prof, loopweights);

    // LLVM loop metadata requires the MDNode's first operand to reference the node itself (replaceOperandWith(0, loopmd)); without the self-reference the loop pass manager asserts on malformed loop MD and refuses to walk our latch
    MDNode* unrolldisable = MDNode::get(c, { MDString::get(c, "llvm.loop.unroll.disable") });
    MDNode* loopmd = MDNode::get(c, { nullptr, unrolldisable });
    loopmd->replaceOperandWith(0, loopmd);
    lbbr->setMetadata(LLVMContext::MD_loop, loopmd);

    counterphi->addIncoming(counternext, loopbody);
    accumphi->addIncoming(accumnext, loopbody);

    for (Instruction* inst : suffix)
    {
        inst->removeFromParent();
        inst->insertInto(afterloop, afterloop->end());
    }
    IRBuilder<> alb(afterloop);
    alb.CreateBr(tail);

    DenseMap<AllocaInst*, Value*> remap;
    BuildStackSlotRemap(f, suffix, Rng, remap);
    IRBuilder<> pb(pollute);
    CloneSuffixWithStackRemap(pb, suffix, remap, BarrierState, Rng);
    pb.CreateBr(tail);

    SmallVector<DominatorTree::UpdateType, 16> updates = {
        {DominatorTree::Insert, bb, loopheader},
        {DominatorTree::Insert, loopheader, loopbody},
        {DominatorTree::Insert, loopheader, pollute},
        {DominatorTree::Insert, loopbody, loopheader},
        {DominatorTree::Insert, loopbody, afterloop},
        {DominatorTree::Insert, afterloop, tail},
        {DominatorTree::Insert, pollute, tail},
        {DominatorTree::Delete, bb, tail},
    };
    dtu.applyUpdates(updates);

    MarkBBProcessed(*bb);
    return true;
}

static void FillSyntheticDecoy(Instruction* termindecoy, ArrayRef<Value*> runtimecontext, std::mt19937_64& rng);

static bool TryEmitLoopClassic(Function& f, BasicBlock* bb, size_t siteidx, DomTreeUpdater& dtu, LoopInfo& li)
{
    (void)li;

    Instruction* insertbefore = PickRandomEligibleInBB(*bb, Rng);
    if (!insertbefore) return false;
    if (insertbefore->isTerminator()) return false;

    LLVMContext& c = f.getContext();
    IntegerType* ity = IntegerType::get(c, 64);

    IRBuilder<> headb(insertbefore);
    std::vector<Value*> harvested = mbagen::GatherAuxValues(headb, dtu.getDomTree(), ity, IdentityV, Rng, CrossWidthPct);
    if (harvested.size() < 1) return false;
    for (Value* v : harvested)
    {
        if (!v || v->getType() != ity) return false;
    }

    const unsigned loopspan = LoopMaxLimit - LoopMinLimit + 1u;
    const uint64_t looplimit = LoopMinLimit + (uint64_t)(Rng() % loopspan);
    Value* limitval = mbagen::InsertFoldBarrier(headb, ConstantInt::get(ity, looplimit), BarrierState);

    BasicBlock* tail = bb->splitBasicBlock(insertbefore, bb->getName() + ".NLMBAOpaqueLCTail");

    BasicBlock* loopheader = BasicBlock::Create(c, "NLMBAOpaqueLCH." + std::to_string(siteidx), &f, tail);
    BasicBlock* loopbody = BasicBlock::Create(c, "NLMBAOpaqueLCB." + std::to_string(siteidx), &f, tail);
    BasicBlock* pollute = BasicBlock::Create(c, "NLMBAOpaqueLCP." + std::to_string(siteidx), &f, tail);

    Instruction* oldterm = bb->getTerminator();
    oldterm->eraseFromParent();
    IRBuilder<> bbb(bb);
    bbb.CreateBr(loopheader);

    IRBuilder<> lhb(loopheader);
    PHINode* counterphi = lhb.CreatePHI(ity, 2, "Counter");
    PHINode* accumphi = lhb.CreatePHI(ity, 2, "Accum");
    counterphi->addIncoming(ConstantInt::get(ity, 0), bb);
    accumphi->addIncoming(harvested[0], bb);

    SmallVector<Value*, 4> loopinputs;
    loopinputs.push_back(counterphi);
    loopinputs.push_back(accumphi);
    for (size_t i = 1; i < harvested.size() && loopinputs.size() < IdentityV; ++i) loopinputs.push_back(harvested[i]);
    while (loopinputs.size() < IdentityV) loopinputs.push_back(harvested[0]);

    Value* lhs = mbagen::EmitNonlinearOpaqueEquation(lhb, loopinputs, ity, BarrierState, Rng, IdentityV, TierFromFlag(IdentityTierFlag), IdentityGroupCount, IdentityVerifySamples, IdentityMaxRetries);
    if (!lhs || isa<ConstantInt>(lhs))
    {
        // same cleanup ordering as TryEmitLoop. phi erase before bb repoint before loopheader erase, or dangling use and live predecessor asserts fire in debug builds
        counterphi->eraseFromParent();
        accumphi->eraseFromParent();
        bb->getTerminator()->eraseFromParent();
        IRBuilder<> restoreb(bb);
        restoreb.CreateBr(tail);
        loopheader->eraseFromParent();
        loopbody->eraseFromParent();
        pollute->eraseFromParent();
        return false;
    }

    const unsigned depthspan = OuterWrapMaxDepth - OuterWrapMinDepth + 1u;
    const unsigned wrapdepth = OuterWrapMinDepth + (unsigned)(Rng() % depthspan);
    lhs = ApplyIdentityPreservingWrap(lhb, lhs, ity, BarrierState, Rng, wrapdepth);

    bool condalwaystrue = false;
    Value* condok = EmitCompareRecipe(lhb, lhs, ity, BarrierState, Rng, condalwaystrue);

    MDBuilder mdb(c);
    BasicBlock* okdest = nullptr;
    BasicBlock* faildest = nullptr;
    MDNode* okweights = nullptr;
    if (condalwaystrue)
    {
        okdest = loopbody;
        faildest = pollute;
        okweights = mdb.createBranchWeights(100000u, 1u);
    }
    else
    {
        okdest = pollute;
        faildest = loopbody;
        okweights = mdb.createBranchWeights(1u, 100000u);
    }
    BranchInst* lhbr = lhb.CreateCondBr(condok, okdest, faildest);
    lhbr->setMetadata(LLVMContext::MD_prof, okweights);

    IRBuilder<> lbb(loopbody);
    Value* counternext = lbb.CreateAdd(counterphi, ConstantInt::get(ity, 1), "CounterNext");
    const uint64_t accumk = (uint64_t)Rng() | 1ull;
    Value* accummul = lbb.CreateMul(counterphi, ConstantInt::get(ity, accumk), "AccumMul");
    Value* accumnext = lbb.CreateXor(accumphi, accummul, "AccumNext");
    Value* exitcond = lbb.CreateICmpULT(counternext, limitval, "ExitCond");
    MDNode* loopweights = mdb.createBranchWeights(100000u, 1u);
    BranchInst* lbbr = lbb.CreateCondBr(exitcond, loopheader, tail);
    lbbr->setMetadata(LLVMContext::MD_prof, loopweights);

    MDNode* unrolldisable = MDNode::get(c, { MDString::get(c, "llvm.loop.unroll.disable") });
    MDNode* loopmd = MDNode::get(c, { nullptr, unrolldisable });
    loopmd->replaceOperandWith(0, loopmd);
    lbbr->setMetadata(LLVMContext::MD_loop, loopmd);

    counterphi->addIncoming(counternext, loopbody);
    accumphi->addIncoming(accumnext, loopbody);

    // the pollute branch's terminator MUST be created before FillSyntheticDecoy runs so the decoy filler has a valid insert before anchor in a terminated block; without the terminator in place the IRBuilder asserts in debug builds and in release emits into the wrong block
    IRBuilder<> pb(pollute);
    pb.CreateBr(tail);
    std::mt19937_64 localrng(Rng());
    FillSyntheticDecoy(pollute->getTerminator(), ArrayRef<Value*>(harvested), localrng);

    SmallVector<DominatorTree::UpdateType, 16> updates = {
        {DominatorTree::Insert, bb, loopheader},
        {DominatorTree::Insert, loopheader, loopbody},
        {DominatorTree::Insert, loopheader, pollute},
        {DominatorTree::Insert, loopbody, loopheader},
        {DominatorTree::Insert, loopbody, tail},
        {DominatorTree::Insert, pollute, tail},
        {DominatorTree::Delete, bb, tail},
    };
    dtu.applyUpdates(updates);

    MarkBBProcessed(*bb);
    return true;
}

static bool PickDonorWindow(Function& f, BasicBlock* excludebb, unsigned mincount, unsigned maxcount, std::mt19937_64& rng, SmallVectorImpl<Instruction*>& outwindow)
{
    outwindow.clear();
    SmallVector<BasicBlock*, 32> candidates;
    BasicBlock* entry = &f.getEntryBlock();
    for (BasicBlock& bb : f)
    {
        if (&bb == excludebb) continue;
        if (&bb == entry) continue;
        if (bb.isEHPad()) continue;
        if (IsOurBBName(bb.getName())) continue;
        unsigned safecount = 0;
        for (Instruction& i : bb)
        {
            if (IsSafeInstructionToClone(i)) ++safecount;
        }
        if (safecount >= mincount) candidates.push_back(&bb);
    }
    if (candidates.empty()) return false;

    BasicBlock* donor = candidates[(size_t)(rng() % candidates.size())];
    SmallVector<Instruction*, 32> safe;
    for (Instruction& i : *donor)
    {
        if (IsSafeInstructionToClone(i)) safe.push_back(&i);
    }
    if (safe.size() < mincount) return false;

    const unsigned cap = (maxcount < (unsigned)safe.size()) ? maxcount : (unsigned)safe.size();
    const unsigned span = cap - mincount + 1u;
    const unsigned target = mincount + (unsigned)(rng() % span);
    const unsigned startmax = (unsigned)safe.size() - target;
    const unsigned start = (unsigned)(rng() % (startmax + 1u));

    for (unsigned k = start; k < start + target; ++k) outwindow.push_back(safe[k]);
    return true;
}

static bool CloneSampleIntoDecoy(IRBuilder<>& b, ArrayRef<Instruction*> sampled, const DenseMap<AllocaInst*, Value*>& stackremap, ArrayRef<Value*> harvestedctx, std::mt19937_64& rng)
{
    DenseMap<Value*, Value*> valmap;
    for (Instruction* orig : sampled)
    {
        Instruction* cloned = orig->clone();
        cloned->setName(orig->getName() + ".Decoy");
        SmallVector<std::pair<unsigned, MDNode*>, 4> allmd;
        cloned->getAllMetadata(allmd);
        for (auto& p : allmd) cloned->setMetadata(p.first, nullptr);
        for (unsigned opidx = 0; opidx < cloned->getNumOperands(); ++opidx)
        {
            Value* op = cloned->getOperand(opidx);
            if (!op) continue;
            auto vmit = valmap.find(op);
            if (vmit != valmap.end()) { cloned->setOperand(opidx, vmit->second); continue; }
            if (auto* a = dyn_cast<AllocaInst>(op))
            {
                auto srit = stackremap.find(a);
                if (srit != stackremap.end() && srit->second != (Value*)a) cloned->setOperand(opidx, srit->second);
                continue;
            }
            if (isa<Constant>(op)) continue;
            if (isa<Argument>(op)) continue;
            if (isa<BasicBlock>(op)) continue;
            if (isa<MetadataAsValue>(op)) continue;
            Type* ty = op->getType();
            Value* sub = nullptr;
            if (ty->isIntegerTy())
            {
                for (Value* h : harvestedctx)
                {
                    if (h && h->getType() == ty) { sub = h; break; }
                }
                if (!sub) sub = ConstantInt::get(ty, (uint64_t)rng());
            }
            else if (ty->isPointerTy())
            {
                sub = ConstantPointerNull::get(cast<PointerType>(ty));
            }
            else
            {
                sub = UndefValue::get(ty);
            }
            cloned->setOperand(opidx, sub);
        }
        b.Insert(cloned);
        valmap[orig] = cloned;
    }
    return true;
}

static bool TryFillSampledDecoy(Function& f, BasicBlock* excludebb, Instruction* termindecoy, ArrayRef<Value*> harvestedctx, std::mt19937_64& rng)
{
    SmallVector<Instruction*, 16> window;
    if (!PickDonorWindow(f, excludebb, SampledMinInsts, SampledMaxInsts, rng, window)) return false;
    if (window.empty()) return false;
    DenseMap<AllocaInst*, Value*> remap;
    BuildStackSlotRemap(f, window, rng, remap);
    IRBuilder<> b(termindecoy);
    return CloneSampleIntoDecoy(b, window, remap, harvestedctx, rng);
}

static GlobalVariable* GetOrCreateBogusSinkInPool(Module& m, unsigned idx)
{
    const unsigned i = idx % BogusSinkPoolSize;
    const std::string name = ".NLMBAOpaqueBogusSink." + std::to_string(i);
    if (auto* existing = m.getGlobalVariable(name)) return existing;
    LLVMContext& c = m.getContext();
    IntegerType* i64 = IntegerType::get(c, 64);
    auto* gv = new GlobalVariable(m, i64, false, GlobalValue::InternalLinkage, ConstantInt::get(i64, 0), name);
    gv->setUnnamedAddr(GlobalValue::UnnamedAddr::None);
    gv->setAlignment(Align(8));
    return gv;
}

static void FillSyntheticDecoy(Instruction* termindecoy, ArrayRef<Value*> runtimecontext, std::mt19937_64& rng)
{
    IRBuilder<> builder(termindecoy);
    LLVMContext& c = builder.getContext();
    IntegerType* i64 = IntegerType::get(c, 64);
    Module* m = termindecoy->getFunction()->getParent();

    const unsigned nsinks = 1u + (unsigned)(rng() % BogusMaxExtraSinkLoads);
    SmallVector<GlobalVariable*, 4> sinks;
    sinks.reserve(nsinks);
    for (unsigned i = 0; i < nsinks; ++i) sinks.push_back(GetOrCreateBogusSinkInPool(*m, (unsigned)rng()));

    LoadInst* ld0 = builder.CreateLoad(i64, sinks[0], true, "BogusLd0");
    ld0->setAlignment(Align(8));
    Value* acc = ld0;

    for (unsigned i = 1; i < nsinks; ++i)
    {
        LoadInst* lx = builder.CreateLoad(i64, sinks[i], true, "BogusLdx");
        lx->setAlignment(Align(8));
        const unsigned k = (unsigned)(rng() % 4u);
        if (k == 0) acc = builder.CreateXor(acc, lx, "BogusMXor");
        else if (k == 1) acc = builder.CreateAdd(acc, lx, "BogusMAdd");
        else if (k == 2) acc = builder.CreateAnd(acc, lx, "BogusMAnd");
        else acc = builder.CreateOr(acc, lx, "BogusMOr");
    }

    if (!runtimecontext.empty() && (rng() & 1u) != 0u)
    {
        for (Value* rv : runtimecontext)
        {
            if (!rv || rv->getType() != i64) continue;
            if ((rng() & 3u) != 0u) continue;
            const unsigned k = (unsigned)(rng() % 4u);
            if (k == 0) acc = builder.CreateXor(acc, rv, "BogusRVXor");
            else if (k == 1) acc = builder.CreateAdd(acc, rv, "BogusRVAdd");
            else if (k == 2) acc = builder.CreateSub(acc, rv, "BogusRVSub");
            else acc = builder.CreateOr(acc, rv, "BogusRVOr");
        }
    }

    const unsigned opspan = BogusMaxOps - BogusMinOps + 1u;
    const unsigned opcount = BogusMinOps + (unsigned)(rng() % opspan);
    for (unsigned i = 0; i < opcount; ++i)
    {
        const uint64_t k = (uint64_t)rng() | 1ull;
        Value* kv = ConstantInt::get(i64, k);
        const unsigned kind = (unsigned)(rng() % 8u);
        switch (kind)
        {
            case 0: acc = builder.CreateXor(acc, kv, "BogusX"); break;
            case 1: acc = builder.CreateAdd(acc, kv, "BogusA"); break;
            case 2: acc = builder.CreateSub(acc, kv, "BogusS"); break;
            case 3: acc = builder.CreateMul(acc, kv, "BogusM"); break;
            case 4: acc = builder.CreateOr(acc, kv, "BogusO"); break;
            case 5: acc = builder.CreateAnd(acc, kv, "BogusN"); break;
            case 6:
            {
                const unsigned shamt = 1u + (unsigned)(rng() % 15u);
                acc = builder.CreateShl(acc, ConstantInt::get(i64, shamt), "BogusShl");
                break;
            }
            case 7:
            default:
            {
                const unsigned shamt = 1u + (unsigned)(rng() % 15u);
                acc = builder.CreateLShr(acc, ConstantInt::get(i64, shamt), "BogusShr");
                break;
            }
        }
    }

    GlobalVariable* primary = sinks[(size_t)(rng() % sinks.size())];
    StoreInst* st = builder.CreateStore(acc, primary);
    st->setVolatile(true);
    st->setAlignment(Align(8));

    if ((unsigned)(rng() % 100u) < BogusMultiStoreChancePct && sinks.size() > 1)
    {
        for (GlobalVariable* s : sinks)
        {
            if (s == primary) continue;
            if ((rng() & 1u) != 0u) continue;
            Value* alt = builder.CreateXor(acc, ConstantInt::get(i64, (uint64_t)rng() | 1ull), "BogusAlt");
            StoreInst* s2 = builder.CreateStore(alt, s);
            s2->setVolatile(true);
            s2->setAlignment(Align(8));
        }
    }
}

static void FillClassicDecoyBlock(Function& f, BasicBlock* excludebb, Instruction* termindecoy, ArrayRef<Value*> harvestedctx, std::mt19937_64& rng)
{
    const bool prefersampled = (unsigned)(rng() % 100u) < SampledDecoyPct;
    if (prefersampled && TryFillSampledDecoy(f, excludebb, termindecoy, harvestedctx, rng)) return;
    FillSyntheticDecoy(termindecoy, harvestedctx, rng);
}

static bool TryEmitClassic(Function& f, BasicBlock* bb, size_t siteidx, DomTreeUpdater& dtu, LoopInfo& li)
{
    Instruction* insertbefore = PickRandomEligibleInBB(*bb, Rng);
    if (!insertbefore) return false;
    if (insertbefore->isTerminator()) return false;

    LLVMContext& c = f.getContext();
    IntegerType* ity = IntegerType::get(c, 64);
    IRBuilder<> builder(insertbefore);

    std::vector<Value*> harvested = mbagen::GatherAuxValues(builder, dtu.getDomTree(), ity, IdentityV, Rng, CrossWidthPct);
    if (harvested.size() < 1) return false;
    for (Value* v : harvested)
    {
        if (!v || v->getType() != ity) return false;
    }

    Value* lhs = mbagen::EmitNonlinearOpaqueEquation(builder, harvested, ity, BarrierState, Rng, IdentityV, TierFromFlag(IdentityTierFlag), IdentityGroupCount, IdentityVerifySamples, IdentityMaxRetries);
    if (!lhs || isa<ConstantInt>(lhs)) return false;

    const unsigned depthspan = OuterWrapMaxDepth - OuterWrapMinDepth + 1u;
    const unsigned wrapdepth = OuterWrapMinDepth + (unsigned)(Rng() % depthspan);
    lhs = ApplyIdentityPreservingWrap(builder, lhs, ity, BarrierState, Rng, wrapdepth);

    bool condalwaystrue = false;
    Value* cond = EmitCompareRecipe(builder, lhs, ity, BarrierState, Rng, condalwaystrue);

    MDBuilder mdb(c);
    MDNode* weights = mdb.createBranchWeights(1u, 100000u);
    Value* deadcond = condalwaystrue ? builder.CreateXor(cond, ConstantInt::getTrue(c), "Inv") : cond;

    Instruction* decoyterm = SplitBlockAndInsertIfThen(deadcond, insertbefore, false, weights, &dtu, &li, nullptr);
    if (!decoyterm) return false;

    BasicBlock* decoy = decoyterm->getParent();
    decoy->setName(".NLMBAOpaqueDecoy." + std::to_string(siteidx));

    std::mt19937_64 localrng(Rng());
    FillClassicDecoyBlock(f, bb, decoyterm, ArrayRef<Value*>(harvested), localrng);

    MarkBBProcessed(*bb);
    return true;
}

static bool ProcessOneBB(Function& f, BasicBlock* bb, size_t siteidx, DomTreeUpdater& dtu, LoopInfo& li)
{
    if (!bb) return false;
    if (bb->getParent() != &f) return false;
    if (SkipLoops && li.getLoopFor(bb) != nullptr) return false;
    if (!DensityGateOpen(f, siteidx)) return false;

    const unsigned roll = (unsigned)(Rng() % 100u);
    unsigned cum = 0;

    cum += LoopModeWeight;
    if (roll < cum)
    {
        if (TryEmitLoop(f, bb, siteidx, dtu, li)) return true;
        if (TryEmitLoopClassic(f, bb, siteidx, dtu, li)) return true;
        if (TryEmitDiamond(f, bb, siteidx, dtu, li)) return true;
        return TryEmitClassic(f, bb, siteidx, dtu, li);
    }

    cum += LoopClassicModeWeight;
    if (roll < cum)
    {
        if (TryEmitLoopClassic(f, bb, siteidx, dtu, li)) return true;
        if (TryEmitLoop(f, bb, siteidx, dtu, li)) return true;
        if (TryEmitDiamond(f, bb, siteidx, dtu, li)) return true;
        return TryEmitClassic(f, bb, siteidx, dtu, li);
    }

    cum += DiamondModeWeight;
    if (roll < cum)
    {
        if (TryEmitDiamond(f, bb, siteidx, dtu, li)) return true;
        if (TryEmitLoop(f, bb, siteidx, dtu, li)) return true;
        if (TryEmitLoopClassic(f, bb, siteidx, dtu, li)) return true;
        return TryEmitClassic(f, bb, siteidx, dtu, li);
    }

    return TryEmitClassic(f, bb, siteidx, dtu, li);
}

static bool ProcessFunction(Function& f)
{
    if (f.isDeclaration()) return false;
    if (HasNoObfuscateAnnotation(f) || HasNoMBAAnnotation(f) || HasNoOpaqueAnnotation(f)) return false;
    if (!HasObfuscateAnnotation(f)) return false;

    bool mutated = false;
    for (unsigned emitted = 0; emitted < PerFunctionCap; ++emitted)
    {
        DominatorTree dt;
        dt.recalculate(f);
        LoopInfo li;
        li.analyze(dt);
        DomTreeUpdater dtu(dt, DomTreeUpdater::UpdateStrategy::Eager);

        BasicBlock* bb = PickNextBB(f);
        if (!bb) break;

        if (ProcessOneBB(f, bb, emitted, dtu, li)) mutated = true;
        else MarkBBProcessed(*bb);
    }
    return mutated;
}

bool RunNonlinearMBAOpaque(Module& m)
{
    if (!NonlinearMBAOpaqueEnable) return false;

    std::random_device rd;
    uint64_t seed = (uint64_t)rd();
    seed ^= (uint64_t)std::chrono::high_resolution_clock::now().time_since_epoch().count();
    seed ^= ((uint64_t)rd()) << 32;
    seed ^= 0x4E4C4D4241515055ULL;
    Rng.seed(seed);

    uint64_t barrierseed = Rng();
    if (barrierseed == 0) barrierseed = 0x4E4C4F50415155ULL;
    BarrierState.Init(&m, BarrierPoolSize, barrierseed, BarrierWeightLegacy, BarrierWeightXor, BarrierWeightAdd, BarrierWeightSub, ".mba.barrier.nlmbaopq");

    bool mutated = false;
    for (Function& f : m) mutated |= ProcessFunction(f);

    mbagen::BarrierFinalizeModule(BarrierState);
    return mutated;
}

PreservedAnalyses NonlinearMBAOpaquePass::run(Module& m, ModuleAnalysisManager&)
{
    bool mutated = RunNonlinearMBAOpaque(m);
    return mutated ? PreservedAnalyses::none() : PreservedAnalyses::all();
}