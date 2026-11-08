#pragma once

#include "llvm/IR/PassManager.h"
#include "llvm/Passes/PassPlugin.h"
#include "llvm/Support/CommandLine.h"

struct CFGNanoPass : llvm::PassInfoMixin<CFGNanoPass>
{
    llvm::PreservedAnalyses run(llvm::Module& m, llvm::ModuleAnalysisManager&);
};

bool RunCFGNano(llvm::Module& m);

extern llvm::cl::opt<bool> CFGNanoEnable;