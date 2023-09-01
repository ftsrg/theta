//
// Created by solarowl on 3/30/21.
//

#include "CPipeline.h"
#include "../passes/gazer/Passes.h"
#include "../passes/gazer/UndefToNondet.h"
#include "../passes/ToposortPass.h"
#include "../passes/EliminateGepPass.h"
#include "../passes/BranchDbgCallPass.h"
#include "../passes/EliminateVariables.h"
#include "../passes/EliminatePhiNodes.h"
#include "../passes/TransformHandlesToIntPass.h"
#include <llvm/IR/IRPrintingPasses.h>
// #include "../passes/modified/SimplifyCFGModifiedPass.h"

CPipeline::CPipeline(std::string _filename, std::string _clangCLI) {
    std::string filenameExtension = _filename.substr(_filename.length() - 2, _filename.length());
    if (!(filenameExtension.compare(".c") || filenameExtension.compare(".i"))) {
        std::cerr << "Error: Input file should be a .c or .i file!" << std::endl;
        abort();
    }

    this->clangCli = _clangCLI;
    this->filename = _filename;
    this->bcFilename = filename.substr(0, filename.length() - 2) + ".bc";

    //std::cout << this->bcFilename << std::endl;
    this->clangArgs = std::vector < llvm::StringRef > {
            this->clangCli,
            "-g",
            "-c",
            "-O0",
            "-emit-llvm",
            "-Xclang", "-disable-O0-optnone",
            "-o", this->bcFilename,
            this->filename
    };
}

void CPipeline::executeClang() {
    std::string clangErrors;

    int returnCode = llvm::sys::ExecuteAndWait(
            clangCli,
            clangArgs,
            llvm::None,
            llvm::None,
            0,
            0,
            &clangErrors
    );

    if (returnCode == -1) {
        llvm::errs() << "ERROR: failed to execute clang: "
                     << (clangErrors.empty() ? "Unknown error." : clangErrors) << "\n";
        abort();
    }

    if (returnCode != 0) {
        llvm::errs() << "ERROR: clang exited with a non-zero exit code.\n";
        abort();
    }

    llvm::SMDiagnostic error;

    this->module = parseIRFile(bcFilename, error, context);

    if (module == nullptr) {
        std::cout << "Error while parsing: null module!" << std::endl;
        abort();
    }
}

void CPipeline::executeOptimizationPasses() {
    llvm::legacy::PassManager pm;
    llvm::initializeAnalysis(*llvm::PassRegistry::getPassRegistry());

    pm.add(createBranchDbgCallPass());

    auto mainPtr = module->getFunction("main");
    if (mainPtr == nullptr) {
        std::cerr << "ERROR: entry function (main) not found" << std::endl;
        abort();
    }

    if (PassGroupManager::enableInlining) {
        pm.add(llvm::createInternalizePass([this](auto &gv) {
            if (auto fun = llvm::dyn_cast<llvm::Function>(&gv)) {
                return module->getFunction("main") == fun;
            } else if(auto gvar = llvm::dyn_cast<llvm::GlobalVariable>(&gv)) {
                return true;
            }
            return false;
        }));
        // For now we hardcode main as the entry function and all as inline level
        pm.add(gazer::createSimpleInlinerPass(*mainPtr, gazer::InlineLevel::All));
        pm.add(llvm::createGlobalDCEPass()); // Remove dead functions
    

        // Transform the generated alloca instructions into registers
        pm.add(llvm::createPromoteMemoryToRegisterPass());
    }

    if (PassGroupManager::enableOptimizations) {
        // Start with some metadata-based typed AA
        pm.add(llvm::createTypeBasedAAWrapperPass());
        pm.add(llvm::createScopedNoAliasAAWrapperPass());
        pm.add(llvm::createBasicAAWrapperPass());

        // Split call sites under conditionals
        pm.add(llvm::createCallSiteSplittingPass());

        // Do some inter-procedural reductions
        pm.add(llvm::createIPSCCPPass());
        pm.add(llvm::createGlobalOptimizerPass());
        pm.add(llvm::createDeadArgEliminationPass());

        // Clean up
        pm.add(llvm::createInstructionCombiningPass());
        pm.add(createEliminationPass()); // must be after createInstructionCombiningPass, otherwise weird things happen

        // Note: CFG simplifier can do some problematic stuff, like creating logical binary ops from phi node - icmp combinations
        /*
        llvm::SimplifyCFGOptions options = llvm::SimplifyCFGOptions(1, false, false, true, false, nullptr, false, false);
        llvm::Pass* scfgpass = new llvm::SimplifyCFGPass(options);
        pm.add(scfgpass);
        llvm::createCFGSimplificationPass()
        */

        // pm.add(llvm::createCFGSimplificationPass());

        // pm.add(llvm::createSROAPass());
        // pm.add(gazer::createPromoteUndefsPass()); // SROA may introduce new undef values, so we run another promote undef pass after it

        // // pm.add(llvm::createPrintModulePass(llvm::outs()));
        // pm.add(llvm::createEarlyCSEPass());

        // // pm.add(llvm::createCFGSimplificationPass());
        // pm.add(llvm::createAggressiveInstCombinerPass());
        // pm.add(llvm::createInstructionCombiningPass());

        // // Try to remove irreducible control flow
        // pm.add(llvm::createStructurizeCFGPass());

        // // Optimize loops
        // pm.add(llvm::createLoopInstSimplifyPass());
        // pm.add(llvm::createLoopSimplifyCFGPass());
        // pm.add(llvm::createLoopRotatePass());
        // pm.add(llvm::createLICMPass());

        // // pm.add(llvm::createCFGSimplificationPass());
        // pm.add(llvm::createInstructionCombiningPass());

        // pm.add(llvm::createIndVarSimplifyPass());
        // pm.add(llvm::createLoopStrengthReducePass()); // needed by indvarsimplify (see LLVM passes reference manual)
        // pm.add(llvm::createLoopDeletionPass());

        // pm.add(llvm::createNewGVNPass());

    }
    pm.add(createEliminateGepPass());

    // Note: CFG simplifier can do some problematic stuff, like creating logical binary ops from phi node - icmp combinations
    // more problems: we can lose assumption line metadata on this as well
    // and if used so late, it can merge icmps into a logical or/other op and that probably won't be usable when giving cex
    // pm.add(llvm::createCFGSimplificationPass()); // simplifies CFG of a function, (good as a clean up?), later/sooner?

    // "cleanup":
    if (PassGroupManager::enableCleanupPasses) {
        pm.add(llvm::createInstructionCombiningPass()); // algebraic simplification (does not modify CFG), -instcombine
        // https://llvm.org/doxygen/classllvm_1_1SimplifyCFGPass.html#details

        pm.add(llvm::createDeadArgEliminationPass()); // -deadargelim
        pm.add(llvm::createRedundantDbgInstEliminationPass()); // -die (I mean the LLVM flag - not as a threat)
        pm.add(gazer::createPromoteUndefsPass()); // cleanups can bring undefs
    }

    pm.add(createToposortPass());
    // pm.add(createPhiEliminationPass());

    // pm.add(llvm::createDemoteRegisterToMemoryPass());
    pm.add(gazer::createPromoteUndefsPass()); // cleanups can bring undefs

    pm.add(createTransformHandlesToIntPass());
    pm.add(llvm::createStripDeadPrototypesPass());

    // FatalErrors = false - it won't kill our process for each error (maybe for some?)
    // it will print, what it finds to stderr
    pm.add(llvm::createVerifierPass(false));

    pm.run(*module);
}

std::unique_ptr <llvm::Module> CPipeline::processCProgram() {
    executeClang();
    executeOptimizationPasses();
    return std::move(module); // we move this out of here - can be done only once!
}