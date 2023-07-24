//
// Created by solarowl on 3/30/21.
//

#ifndef JNI_LIBRARY_CPIPELINE_H
#define JNI_LIBRARY_CPIPELINE_H

#include "../types/Module.h"
#include "PassGroupManager.h"
#include <llvm/Transforms/Scalar/SimplifyCFG.h>
#include <llvm/Transforms/Utils/Local.h>

class CPipeline {
private:
    std::vector <llvm::StringRef> clangArgs;
    std::string filename;
    std::string bcFilename;
    std::string clangCli;
    std::unique_ptr <llvm::Module> module = nullptr; // parsed from .bc at the end of executeClang

    void executeClang();

    void executeOptimizationPasses();

public:
    CPipeline(std::string filename, std::string clangCLI = "clang"); // it will run clang & passes on the C file
    void addClangArg(std::string arg) { clangArgs.push_back(arg); } // does not check, if arg was already added!
    std::unique_ptr <llvm::Module> processCProgram();
};


#endif //JNI_LIBRARY_CPIPELINE_H
