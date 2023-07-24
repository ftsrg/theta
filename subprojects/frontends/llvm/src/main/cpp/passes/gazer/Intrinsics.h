//==-------------------------------------------------------------*- C++ -*--==//
//
// Copyright 2019 Contributors to the Gazer project
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
//
//===----------------------------------------------------------------------===//
/// \file This file describes the various intrinsic functions that
/// Gazer uses for instrumentation.
#ifndef _GAZER_LLVM_INSTRUMENTATION_INTRINSICS_H
#define _GAZER_LLVM_INSTRUMENTATION_INTRINSICS_H

#include <llvm/IR/Instructions.h>
#include <llvm/IR/DebugInfoMetadata.h>

#include <string_view>

namespace gazer {

    class GazerIntrinsic {
    public:
        /*
        static constexpr char FunctionEntryPrefix[] = "gazer.function.entry";
        static constexpr char FunctionReturnVoidName[] = "gazer.function.return_void";
        static constexpr char FunctionCallReturnedName[] = "gazer.function.call_returned";
        static constexpr char FunctionReturnValuePrefix[] = "gazer.function.return_value.";
        */
        // static constexpr char InlinedGlobalWritePrefix[] = "gazer.inlined_global.write."; // TODO debug this - undefined reference to this from Intrinsics.cpp

        /*
        static constexpr char NoOverflowPrefix[] = "gazer.no_overflow";

        static constexpr char SAddNoOverflowPrefix[] = "gazer.no_overflow.sadd.";
        static constexpr char SSubNoOverflowPrefix[] = "gazer.no_overflow.ssub.";
        static constexpr char SMulNoOverflowPrefix[] = "gazer.no_overflow.smul.";
        static constexpr char SDivNoOverflowPrefix[] = "gazer.no_overflow.sdiv.";

        static constexpr char UAddNoOverflowPrefix[] = "gazer.no_overflow.uadd.";
        static constexpr char USubNoOverflowPrefix[] = "gazer.no_overflow.usub.";
        static constexpr char UMulNoOverflowPrefix[] = "gazer.no_overflow.umul.";

        enum class Overflow
        {
            SAdd, UAdd, SSub, USub, SMul, UMul
        };
        */
    public:
        static llvm::CallInst *CreateInlinedGlobalWrite(llvm::Value *value, llvm::DIGlobalVariable *gv);
        //static llvm::CallInst* CreateFunctionEntry(llvm::Module& module, llvm::DISubprogram* dsp = nullptr);

    public:
        /// Returns a 'gazer.function.entry(metadata fn_name, args...)' intrinsic.
        //static llvm::FunctionCallee GetOrInsertFunctionEntry(llvm::Module& module, llvm::ArrayRef<llvm::Type*> args);

        /// Returns a 'gazer.function.return_void(metadata fn_name)' intrinsic.
        //static llvm::FunctionCallee GetOrInsertFunctionReturnVoid(llvm::Module& module);

        /// Returns a 'gazer.function.call_returned(metadata fn_name)' intrinsic.
        //static llvm::FunctionCallee GetOrInsertFunctionCallReturned(llvm::Module& module);

        /// Returns a 'gazer.function.return_value.T(metadata fn_name, T retval)' intrinsic,
        /// where 'T' is the given return type.
        //static llvm::FunctionCallee GetOrInsertFunctionReturnValue(llvm::Module& module, llvm::Type* type);

        /// Returns a 'gazer.inlined_global_write.T(T value, metadata gv_name)' intrinsic.
        static llvm::FunctionCallee GetOrInsertInlinedGlobalWrite(llvm::Module &module, llvm::Type *type);

        /// Returns a 'gazer.KIND.no_overflow.T(T left, T right)' intrinsic.
        //static llvm::FunctionCallee GetOrInsertOverflowCheck(llvm::Module& module, Overflow kind, llvm::Type* type);
    };

}

#endif