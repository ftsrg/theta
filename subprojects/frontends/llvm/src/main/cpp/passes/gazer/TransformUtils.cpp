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

#include "TransformUtils.h"

#include <llvm/ADT/SCCIterator.h>

namespace gazer {

    bool isRecursive(llvm::CallGraphNode *target) {
        // We wish to identify the cases of direct AND indirect static
        // recursion. We do not bother with function pointers and
        // external calls.
        auto begin = llvm::scc_begin(target);
        auto end = llvm::scc_end(target);

        for (auto it = begin; it != end; ++it) {
            if (it.hasCycle()) {
                return true;
            }
        }

        return false;
    }

}