//
// Created by solarowl on 4/2/21.
//

#ifndef JNI_LIBRARY_LLVMIMPORTS_H
#define JNI_LIBRARY_LLVMIMPORTS_H

#include <llvm/IR/Module.h>
#include <llvm/IR/LLVMContext.h>
#include <llvm/IR/GlobalVariable.h>
#include <llvm/IR/InstrTypes.h>
#include <llvm/IR/Verifier.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/Metadata.h>
#include <llvm/IR/DebugInfoMetadata.h>
#include <llvm/IR/Argument.h>
#include <llvm/IR/LegacyPassManager.h>
#include "llvm/IR/Operator.h"

#include <llvm/IRReader/IRReader.h>
#include <llvm/ADT/SmallVector.h>
#include <llvm/Support/SourceMgr.h>
#include <llvm/Support/raw_ostream.h>
#include <llvm/Support/CommandLine.h>
#include <llvm/Support/Program.h>

#include <llvm/Analysis/ScopedNoAliasAA.h>
#include <llvm/Analysis/TypeBasedAliasAnalysis.h>
#include <llvm/Analysis/BasicAliasAnalysis.h>
#include <llvm/Analysis/GlobalsModRef.h>
#include <llvm/Analysis/MemorySSA.h>
#include <llvm/Transforms/Utils.h>
#include <llvm/Transforms/Scalar.h>
#include <llvm/Transforms/IPO.h>
#include <llvm/Transforms/InstCombine/InstCombine.h>
#include <llvm/Transforms/AggressiveInstCombine/AggressiveInstCombine.h>
#include <llvm/Transforms/Utils/UnifyFunctionExitNodes.h>
#include <llvm/InitializePasses.h>

#endif //JNI_LIBRARY_LLVMIMPORTS_H
