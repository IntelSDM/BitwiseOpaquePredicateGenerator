#pragma once

#include "AtomTree.h"
#include "FoldBarrier.h"
#include "MBABasis.h"

#include "llvm/ADT/ArrayRef.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/Value.h"

#include <cassert>
#include <cstdint>
#include <memory>
#include <random>
#include <vector>

namespace mbagen
{

enum class NLExprOp : uint8_t
{
    LHS,
    K,
    Not,
    And,
    Or,
    Xor,
    Add,
    Sub,
    Mul,
    Shl,
};

struct NLExprNode;
using NLExprPtr = std::shared_ptr<const NLExprNode>;

struct NLExprNode
{
    NLExprOp Op;
    unsigned KIdx = 0;
    unsigned Shamt = 0;
    std::vector<NLExprPtr> Kids;
};

inline NLExprPtr MakeNLLHS()
{
    auto n = std::make_shared<NLExprNode>();
    n->Op = NLExprOp::LHS;
    return n;
}

inline NLExprPtr MakeNLKSlot(unsigned i)
{
    auto n = std::make_shared<NLExprNode>();
    n->Op = NLExprOp::K;
    n->KIdx = i;
    return n;
}

inline NLExprPtr MakeNLUnary(NLExprOp op, NLExprPtr a)
{
    auto n = std::make_shared<NLExprNode>();
    n->Op = op;
    n->Kids = { std::move(a) };
    return n;
}

inline NLExprPtr MakeNLBin(NLExprOp op, NLExprPtr a, NLExprPtr b)
{
    auto n = std::make_shared<NLExprNode>();
    n->Op = op;
    n->Kids = { std::move(a), std::move(b) };
    return n;
}

inline NLExprPtr MakeNLShl(NLExprPtr a, unsigned shamt)
{
    auto n = std::make_shared<NLExprNode>();
    n->Op = NLExprOp::Shl;
    n->Shamt = shamt;
    n->Kids = { std::move(a) };
    return n;
}

inline void AnalyzeNLExpr(const NLExprNode& t, unsigned& outnumks, bool& outhaslhs)
{
    if (t.Op == NLExprOp::LHS) { outhaslhs = true; return; }
    if (t.Op == NLExprOp::K)
    {
        if (t.KIdx + 1u > outnumks) outnumks = t.KIdx + 1u;
        return;
    }
    for (const auto& k : t.Kids) AnalyzeNLExpr(*k, outnumks, outhaslhs);
}

inline NLExprPtr GenerateNLExprInner(std::mt19937_64& rng, unsigned& kcursor, unsigned depth, unsigned w)
{
    if (depth == 0 || (rng() % 5u) == 0u)
    {
        if ((rng() & 1u) == 0u) return MakeNLLHS();
        return MakeNLKSlot(kcursor++);
    }

    // Shl shift amount MUST sit in [1, w-1] because shamt >= w is LLVM poison and shamt == 0 collapses the Shl to the identity so the op would add no obfuscation value
    const unsigned op = (unsigned)(rng() % 10u);
    switch (op)
    {
        case 0:
            return MakeNLUnary(NLExprOp::Not, GenerateNLExprInner(rng, kcursor, depth - 1u, w));
        case 1:
            return MakeNLBin(NLExprOp::And, GenerateNLExprInner(rng, kcursor, depth - 1u, w), GenerateNLExprInner(rng, kcursor, depth - 1u, w));
        case 2:
            return MakeNLBin(NLExprOp::Or, GenerateNLExprInner(rng, kcursor, depth - 1u, w), GenerateNLExprInner(rng, kcursor, depth - 1u, w));
        case 3:
            return MakeNLBin(NLExprOp::Xor, GenerateNLExprInner(rng, kcursor, depth - 1u, w), GenerateNLExprInner(rng, kcursor, depth - 1u, w));
        case 4:
            return MakeNLBin(NLExprOp::Add, GenerateNLExprInner(rng, kcursor, depth - 1u, w), GenerateNLExprInner(rng, kcursor, depth - 1u, w));
        case 5:
            return MakeNLBin(NLExprOp::Sub, GenerateNLExprInner(rng, kcursor, depth - 1u, w), GenerateNLExprInner(rng, kcursor, depth - 1u, w));
        case 6:
            return MakeNLBin(NLExprOp::Mul, GenerateNLExprInner(rng, kcursor, depth - 1u, w), GenerateNLExprInner(rng, kcursor, depth - 1u, w));
        case 7:
        {
            const unsigned shamt = 1u + (unsigned)(rng() % (w > 1u ? (w - 1u) : 1u));
            return MakeNLShl(GenerateNLExprInner(rng, kcursor, depth - 1u, w), shamt);
        }
        case 8:
            return MakeNLBin(NLExprOp::Xor, GenerateNLExprInner(rng, kcursor, depth - 1u, w), GenerateNLExprInner(rng, kcursor, depth - 1u, w));
        case 9:
        default:
            return MakeNLBin(NLExprOp::Add, GenerateNLExprInner(rng, kcursor, depth - 1u, w), GenerateNLExprInner(rng, kcursor, depth - 1u, w));
    }
}

inline NLExprPtr GenerateNLExpr(std::mt19937_64& rng, unsigned depth, unsigned w, unsigned& outnumks)
{
    unsigned kcursor = 0;
    NLExprPtr tree = GenerateNLExprInner(rng, kcursor, depth, w);

    // without a guaranteed LHS leaf the mixer degenerates to a bare K only expression independent of runtime input, which defeats the family's data-dependency property; folding LHS in at the root via XOR preserves tree correctness and is the cheapest recovery
    unsigned ks = 0;
    bool haslhs = false;
    AnalyzeNLExpr(*tree, ks, haslhs);
    if (!haslhs)
    {
        tree = MakeNLBin(NLExprOp::Xor, MakeNLLHS(), tree);
        ks = 0;
        haslhs = false;
        AnalyzeNLExpr(*tree, ks, haslhs);
    }

    outnumks = ks;
    return tree;
}

inline u64 EvalNLExpr(const NLExprNode& t, u64 lhsval, llvm::ArrayRef<u64> kvals, unsigned w)
{
    switch (t.Op)
    {
        case NLExprOp::LHS: return MaskW(lhsval, w);
        case NLExprOp::K:
            assert(t.KIdx < kvals.size());
            return MaskW(kvals[t.KIdx], w);
        case NLExprOp::Not: return MaskW(~EvalNLExpr(*t.Kids[0], lhsval, kvals, w), w);
        case NLExprOp::And: return MaskW(EvalNLExpr(*t.Kids[0], lhsval, kvals, w) & EvalNLExpr(*t.Kids[1], lhsval, kvals, w), w);
        case NLExprOp::Or:  return MaskW(EvalNLExpr(*t.Kids[0], lhsval, kvals, w) | EvalNLExpr(*t.Kids[1], lhsval, kvals, w), w);
        case NLExprOp::Xor: return MaskW(EvalNLExpr(*t.Kids[0], lhsval, kvals, w) ^ EvalNLExpr(*t.Kids[1], lhsval, kvals, w), w);
        case NLExprOp::Add: return MaskW(EvalNLExpr(*t.Kids[0], lhsval, kvals, w) + EvalNLExpr(*t.Kids[1], lhsval, kvals, w), w);
        case NLExprOp::Sub: return MaskW(EvalNLExpr(*t.Kids[0], lhsval, kvals, w) - EvalNLExpr(*t.Kids[1], lhsval, kvals, w), w);
        case NLExprOp::Mul: return MaskW(EvalNLExpr(*t.Kids[0], lhsval, kvals, w) * EvalNLExpr(*t.Kids[1], lhsval, kvals, w), w);
        case NLExprOp::Shl:
        {
            const u64 v = EvalNLExpr(*t.Kids[0], lhsval, kvals, w);
            return MaskW(v << t.Shamt, w);
        }
    }
    return 0;
}

inline llvm::Value* EmitNLExprIR(const NLExprNode& t, llvm::IRBuilder<>& b, llvm::Value* lhsvalue, llvm::ArrayRef<llvm::Value*> kvalues, llvm::IntegerType* ity)
{
    switch (t.Op)
    {
        case NLExprOp::LHS: return lhsvalue;
        case NLExprOp::K:
            assert(t.KIdx < kvalues.size());
            return kvalues[t.KIdx];
        case NLExprOp::Not:
            return b.CreateNot(EmitNLExprIR(*t.Kids[0], b, lhsvalue, kvalues, ity), "NLExprNot");
        case NLExprOp::And:
            return b.CreateAnd(EmitNLExprIR(*t.Kids[0], b, lhsvalue, kvalues, ity), EmitNLExprIR(*t.Kids[1], b, lhsvalue, kvalues, ity), "NLExprAnd");
        case NLExprOp::Or:
            return b.CreateOr(EmitNLExprIR(*t.Kids[0], b, lhsvalue, kvalues, ity), EmitNLExprIR(*t.Kids[1], b, lhsvalue, kvalues, ity), "NLExprOr");
        case NLExprOp::Xor:
            return b.CreateXor(EmitNLExprIR(*t.Kids[0], b, lhsvalue, kvalues, ity), EmitNLExprIR(*t.Kids[1], b, lhsvalue, kvalues, ity), "NLExprXor");
        case NLExprOp::Add:
            return b.CreateAdd(EmitNLExprIR(*t.Kids[0], b, lhsvalue, kvalues, ity), EmitNLExprIR(*t.Kids[1], b, lhsvalue, kvalues, ity), "NLExprAdd");
        case NLExprOp::Sub:
            return b.CreateSub(EmitNLExprIR(*t.Kids[0], b, lhsvalue, kvalues, ity), EmitNLExprIR(*t.Kids[1], b, lhsvalue, kvalues, ity), "NLExprSub");
        case NLExprOp::Mul:
            return b.CreateMul(EmitNLExprIR(*t.Kids[0], b, lhsvalue, kvalues, ity), EmitNLExprIR(*t.Kids[1], b, lhsvalue, kvalues, ity), "NLExprMul");
        case NLExprOp::Shl:
        {
            llvm::Value* inner = EmitNLExprIR(*t.Kids[0], b, lhsvalue, kvalues, ity);
            return b.CreateShl(inner, llvm::ConstantInt::get(ity, t.Shamt), "NLExprShl");
        }
    }
    return lhsvalue;
}

inline NLExprPtr WrapLHSRecursive(const NLExprPtr& t, std::mt19937_64& rng, unsigned& kcursor)
{
    if (t->Op == NLExprOp::LHS)
    {
        const unsigned kind = (unsigned)(rng() % 5u);
        const unsigned myk = kcursor++;
        switch (kind)
        {
            case 0:
            {
                // both K references MUST point at the same slot index so the symbolic evaluator and the barriered IR load see the identical runtime value; distinct slots would make x + K1 - K2 nonzero at runtime and break the eval at 0 invariant the compare path depends on
                NLExprPtr add = MakeNLBin(NLExprOp::Add, MakeNLLHS(), MakeNLKSlot(myk));
                return MakeNLBin(NLExprOp::Sub, add, MakeNLKSlot(myk));
            }
            case 1:
            {
                NLExprPtr aand = MakeNLBin(NLExprOp::And, MakeNLLHS(), MakeNLKSlot(myk));
                NLExprPtr notk = MakeNLUnary(NLExprOp::Not, MakeNLKSlot(myk));
                NLExprPtr band = MakeNLBin(NLExprOp::And, MakeNLLHS(), notk);
                return MakeNLBin(NLExprOp::Add, aand, band);
            }
            case 2:
            {
                NLExprPtr orv = MakeNLBin(NLExprOp::Or, MakeNLLHS(), MakeNLKSlot(myk));
                return MakeNLBin(NLExprOp::Xor, orv, MakeNLKSlot(myk));
            }
            case 3:
            {
                return MakeNLBin(NLExprOp::Mul, MakeNLLHS(), MakeNLKSlot(myk));
            }
            case 4:
            default:
            {
                NLExprPtr aand = MakeNLBin(NLExprOp::And, MakeNLLHS(), MakeNLKSlot(myk));
                return MakeNLBin(NLExprOp::Xor, MakeNLLHS(), aand);
            }
        }
    }
    if (t->Op == NLExprOp::K) return t;

    auto n = std::make_shared<NLExprNode>();
    n->Op = t->Op;
    n->KIdx = t->KIdx;
    n->Shamt = t->Shamt;
    n->Kids.reserve(t->Kids.size());
    for (const auto& kid : t->Kids) n->Kids.push_back(WrapLHSRecursive(kid, rng, kcursor));
    return n;
}

inline NLExprPtr ApplyLHSMutation(const NLExprPtr& tree, std::mt19937_64& rng, unsigned& numks)
{
    unsigned cursor = numks;
    NLExprPtr mutated = WrapLHSRecursive(tree, rng, cursor);
    numks = cursor;
    return mutated;
}

inline u64 DrawNLFamilyK(std::mt19937_64& rng, unsigned w)
{
    const u64 mask = MaskW(~u64(0), w);
    for (int tries = 0; tries < 16; ++tries)
    {
        const u64 k = rng() & mask;
        if (k == 0 || k == 1 || k == 2) continue;
        if (k == mask || k == (mask - 1) || k == (mask - 2)) continue;
        return k;
    }
    return (rng() | u64(0x100)) & mask;
}

inline llvm::Value* EmitSynthesizedMixer(llvm::IRBuilder<>& b, llvm::Value* runtime, llvm::IntegerType* ity, ModuleBarrierState& bs, std::mt19937_64& rng, unsigned depth = 3, bool applylhsmutation = true)
{
    const unsigned w = ity->getBitWidth();
    unsigned numks = 0;
    NLExprPtr tree = GenerateNLExpr(rng, depth, w, numks);
    if (applylhsmutation) tree = ApplyLHSMutation(tree, rng, numks);

    llvm::SmallVector<llvm::Value*, 8> kvals;
    kvals.reserve(numks);
    for (unsigned i = 0; i < numks; ++i)
    {
        const u64 k = DrawNLFamilyK(rng, w);
        kvals.push_back(InsertFoldBarrier(b, llvm::ConstantInt::get(ity, k), bs));
    }

    return EmitNLExprIR(*tree, b, runtime, kvals, ity);
}

inline llvm::Value* EmitSynthesizedCompare(llvm::IRBuilder<>& b, llvm::Value* lhs, llvm::IntegerType* ity, ModuleBarrierState& bs, std::mt19937_64& rng, bool& outalwaystrue, unsigned depth = 3, bool applylhsmutation = true)
{
    const unsigned w = ity->getBitWidth();
    unsigned numks = 0;
    NLExprPtr tree = GenerateNLExpr(rng, depth, w, numks);
    if (applylhsmutation) tree = ApplyLHSMutation(tree, rng, numks);

    llvm::SmallVector<llvm::Value*, 8> kvalues;
    llvm::SmallVector<u64, 8> kscalars;
    kvalues.reserve(numks);
    kscalars.reserve(numks);
    for (unsigned i = 0; i < numks; ++i)
    {
        const u64 k = DrawNLFamilyK(rng, w);
        kscalars.push_back(k);
        kvalues.push_back(InsertFoldBarrier(b, llvm::ConstantInt::get(ity, k), bs));
    }

    // expected value MUST be computed against the mutated tree the IR emits, not the pre-mutation tree, because the two sides of the compare must evaluate the identical (tree, Ks) tuple; drifting the trees produces a compare that fires the wrong direction and routes real work into the pollute branch
    const u64 expected = EvalNLExpr(*tree, 0, llvm::ArrayRef<u64>(kscalars.data(), kscalars.size()), w);
    llvm::Value* expectedbarrier = InsertFoldBarrier(b, llvm::ConstantInt::get(ity, expected), bs);

    llvm::Value* exprvalue = EmitNLExprIR(*tree, b, lhs, kvalues, ity);

    outalwaystrue = (rng() & 1u) == 0u;
    if (outalwaystrue) return b.CreateICmpEQ(exprvalue, expectedbarrier, "NLExprCmpE");
    return b.CreateICmpNE(exprvalue, expectedbarrier, "NLExprCmpN");
}

inline llvm::Value* EmitSynthesizedCompareEnsemble(llvm::IRBuilder<>& b, llvm::Value* lhs, llvm::IntegerType* ity, ModuleBarrierState& bs, std::mt19937_64& rng, bool& outalwaystrue, unsigned nsubtrees = 3, unsigned subdepth = 2, bool applylhsmutation = true)
{
    assert(nsubtrees >= 1 && "ensemble needs at least one sub-tree");
    const unsigned w = ity->getBitWidth();

    llvm::SmallVector<llvm::Value*, 4> subir;
    llvm::SmallVector<u64, 4> subsym;
    subir.reserve(nsubtrees);
    subsym.reserve(nsubtrees);

    for (unsigned i = 0; i < nsubtrees; ++i)
    {
        unsigned numks = 0;
        NLExprPtr tree = GenerateNLExpr(rng, subdepth, w, numks);
        if (applylhsmutation) tree = ApplyLHSMutation(tree, rng, numks);

        llvm::SmallVector<llvm::Value*, 8> kvalues;
        llvm::SmallVector<u64, 8> kscalars;
        kvalues.reserve(numks);
        kscalars.reserve(numks);
        for (unsigned j = 0; j < numks; ++j)
        {
            const u64 k = DrawNLFamilyK(rng, w);
            kscalars.push_back(k);
            kvalues.push_back(InsertFoldBarrier(b, llvm::ConstantInt::get(ity, k), bs));
        }

        const u64 sv = EvalNLExpr(*tree, 0, llvm::ArrayRef<u64>(kscalars.data(), kscalars.size()), w);
        llvm::Value* iv = EmitNLExprIR(*tree, b, lhs, kvalues, ity);
        subsym.push_back(sv);
        subir.push_back(iv);
    }

    // the symbolic fold MUST consume the same op sequence as the IR fold in the same iteration order so the folded symbolic value equals the folded IR value at runtime; drifting the sequences yields a compare whose RHS does not match the LHS
    llvm::Value* comboir = subir[0];
    u64 combosym = subsym[0];
    for (unsigned i = 1; i < nsubtrees; ++i)
    {
        const unsigned op = (unsigned)(rng() % 6u);
        switch (op)
        {
            case 0:
                comboir = b.CreateAnd(comboir, subir[i], "NLExprEAnd");
                combosym = MaskW(combosym & subsym[i], w);
                break;
            case 1:
                comboir = b.CreateOr(comboir, subir[i], "NLExprEOr");
                combosym = MaskW(combosym | subsym[i], w);
                break;
            case 2:
                comboir = b.CreateXor(comboir, subir[i], "NLExprEXor");
                combosym = MaskW(combosym ^ subsym[i], w);
                break;
            case 3:
                comboir = b.CreateAdd(comboir, subir[i], "NLExprEAdd");
                combosym = MaskW(combosym + subsym[i], w);
                break;
            case 4:
                comboir = b.CreateSub(comboir, subir[i], "NLExprESub");
                combosym = MaskW(combosym - subsym[i], w);
                break;
            case 5:
            default:
                comboir = b.CreateMul(comboir, subir[i], "NLExprEMul");
                combosym = MaskW(combosym * subsym[i], w);
                break;
        }
    }

    llvm::Value* expectedbarrier = InsertFoldBarrier(b, llvm::ConstantInt::get(ity, combosym), bs);
    outalwaystrue = (rng() & 1u) == 0u;
    if (outalwaystrue) return b.CreateICmpEQ(comboir, expectedbarrier, "NLExprECmpE");
    return b.CreateICmpNE(comboir, expectedbarrier, "NLExprECmpN");
}

inline llvm::Value* EmitSynthesizedConstant(llvm::IRBuilder<>& b, llvm::IntegerType* ity, ModuleBarrierState& bs, std::mt19937_64& rng, unsigned depth = 2)
{
    const unsigned w = ity->getBitWidth();
    unsigned numks = 0;
    NLExprPtr tree = GenerateNLExpr(rng, depth, w, numks);

    llvm::SmallVector<llvm::Value*, 8> kvals;
    kvals.reserve(numks);
    for (unsigned i = 0; i < numks; ++i)
    {
        const u64 k = DrawNLFamilyK(rng, w);
        kvals.push_back(InsertFoldBarrier(b, llvm::ConstantInt::get(ity, k), bs));
    }
    // dummy LHS MUST be barriered so LLVM treats the 0 as opaque and cannot constant fold expressions that touch LHS; a bare 0 would let the folder collapse the whole synthesized tree to a compile-time constant and defeat the point of the pollute pass
    llvm::Value* dummylhs = InsertFoldBarrier(b, llvm::ConstantInt::get(ity, 0), bs);
    return EmitNLExprIR(*tree, b, dummylhs, kvals, ity);
}

}