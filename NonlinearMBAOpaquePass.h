#pragma once

#include "llvm/IR/PassManager.h"
#include "llvm/Passes/PassPlugin.h"
#include "llvm/Support/CommandLine.h"

struct NonlinearMBAOpaquePass : llvm::PassInfoMixin<NonlinearMBAOpaquePass>
{
    llvm::PreservedAnalyses run(llvm::Module& m, llvm::ModuleAnalysisManager&);
};

bool RunNonlinearMBAOpaque(llvm::Module& m);

extern llvm::cl::opt<bool> NonlinearMBAOpaqueEnable;