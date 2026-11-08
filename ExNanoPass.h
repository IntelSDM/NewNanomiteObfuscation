#pragma once

#include "llvm/IR/PassManager.h"
#include "llvm/Passes/PassPlugin.h"
#include "llvm/Support/CommandLine.h"

struct ExNanoPass : llvm::PassInfoMixin<ExNanoPass>
{
    llvm::PreservedAnalyses run(llvm::Module& m, llvm::ModuleAnalysisManager&);
};

bool RunExNano(llvm::Module& m);

extern llvm::cl::opt<bool> ExNanoEnable;