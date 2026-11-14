#pragma once

#include "AtomTree.h"
#include "ConstMBA.h"
#include "FoldBarrier.h"
#include "IREmit.h"
#include "IdentityGenerator.h"
#include "LinearMBA.h"
#include "MBABasis.h"
#include "NonlinearOpaqueFamily.h"

#include "llvm/ADT/ArrayRef.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/Value.h"

#include <cassert>
#include <cstdint>
#include <random>
#include <vector>

namespace mbagen
{

inline constexpr unsigned NLMixerDepthMin = 2;
inline constexpr unsigned NLMixerDepthMax = 4;

inline llvm::Value* EmitNLMixer(llvm::IRBuilder<>& b, llvm::Value* x, llvm::IntegerType* ity, ModuleBarrierState& bs, std::mt19937_64& rng)
{
    const unsigned depthspan = NLMixerDepthMax - NLMixerDepthMin + 1u;
    const unsigned depth = NLMixerDepthMin + (unsigned)(rng() % depthspan);
    return EmitSynthesizedMixer(b, x, ity, bs, rng, depth);
}

inline llvm::SmallVector<llvm::Value*, 8> BuildNLAuxFromRuntimes(llvm::IRBuilder<>& b, llvm::ArrayRef<llvm::Value*> runtimes, llvm::IntegerType* ity, unsigned v, ModuleBarrierState& bs, std::mt19937_64& rng)
{
    assert(!runtimes.empty() && "need at least one runtime value to feed the mixers");
    llvm::SmallVector<llvm::Value*, 8> aux;
    aux.reserve(v);
    for (unsigned i = 0; i < v; ++i)
    {
        llvm::Value* x = runtimes[i % runtimes.size()];
        aux.push_back(EmitNLMixer(b, x, ity, bs, rng));
    }
    return aux;
}

inline llvm::Value* EmitNonlinearOpaqueEquation(llvm::IRBuilder<>& b, llvm::ArrayRef<llvm::Value*> runtimes, llvm::IntegerType* ity, ModuleBarrierState& bs, std::mt19937_64& rng, unsigned v = 3, Tier tier = Tier::T8, unsigned groupcount = 3, unsigned verifysamples = 100, unsigned maxretries = 6)
{
    assert(!runtimes.empty() && "nonlinear opaque needs >=1 runtime value for the mixers");
    const unsigned w = ity->getBitWidth();

    GeneratorState state;
    LinearMBAParams params;
    params.AuxVarCount = v;
    params.RealVarCount = 0;
    params.GroupCount = groupcount;
    params.Width = w;
    params.GeneratorPolicyV.TierV = tier;
    params.GenState = &state;
    params.XYPct = 0;

    LinearMBAExpr expr;
    bool haveexpr = false;
    for (unsigned tries = 0; tries < maxretries; ++tries)
    {
        expr = BuildLinearMBA(LinearMBATarget::Zero, 0u, params, rng);
        if (expr.Terms.empty()) continue;
        if (verifysamples > 0)
        {
            std::mt19937_64 vrng(rng());
            if (!VerifyLinear(expr, vrng, (int)verifysamples)) continue;
        }
        haveexpr = true;
        break;
    }
    if (!haveexpr) return llvm::ConstantInt::get(ity, 0);

    llvm::SmallVector<llvm::Value*, 8> aux = BuildNLAuxFromRuntimes(b, runtimes, ity, v, bs, rng);
    if (aux.size() != expr.VAux) return llvm::ConstantInt::get(ity, 0);

    llvm::SmallVector<llvm::Value*, 1> realvalues;
    return EmitLinearMBA(b, expr, realvalues, aux);
}

}