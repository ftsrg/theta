/*
 *  Copyright 2023 Budapest University of Technology and Economics
 *
 *  Licensed under the Apache License, Version 2.0 (the "License");
 *  you may not use this file except in compliance with the License.
 *  You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 *  Unless required by applicable law or agreed to in writing, software
 *  distributed under the License is distributed on an "AS IS" BASIS,
 *  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *  See the License for the specific language governing permissions and
 *  limitations under the License.
 */

package hu.bme.mit.theta.llvm2xcfa.handlers.concrete;

import hu.bme.mit.theta.llvm2xcfa.LlvmMetadata;
import hu.bme.mit.theta.llvm2xcfa.handlers.BaseInstructionHandler;
import hu.bme.mit.theta.llvm2xcfa.handlers.Instruction;
import hu.bme.mit.theta.llvm2xcfa.handlers.states.BlockState;
import hu.bme.mit.theta.llvm2xcfa.handlers.states.FunctionState;
import hu.bme.mit.theta.llvm2xcfa.handlers.states.GlobalState;
import hu.bme.mit.theta.xcfa.model.NopLabel;
import hu.bme.mit.theta.xcfa.model.XcfaEdge;
import hu.bme.mit.theta.xcfa.model.XcfaLocation;

import java.util.Collection;
import java.util.List;

public class BuiltinFunctionHandler extends BaseInstructionHandler {
    private final static Collection<String> SVCOMP_ERROR_FUNCTIONS = List.of("__assert_fail", "__VERIFIER_error", "abort", "reach_error");
    private final static Collection<String> SVCOMP_NEWTHREAD_FUNCTIONS = List.of("theta_pthread_create");
    private final static Collection<String> SVCOMP_JOINTHREAD_FUNCTIONS = List.of("pthread_join");
    private final static Collection<String> SVCOMP_ATOMIC_BEGIN = List.of("__VERIFIER_atomic_begin");
    private final static Collection<String> SVCOMP_ATOMIC_END = List.of("__VERIFIER_atomic_end");
    private final static Collection<String> ATOMIC_READ = List.of("atomic_load_explicit");
    private final static Collection<String> ATOMIC_WRITE = List.of("atomic_store_explicit");


    @Override
    public void handleInstruction(Instruction instruction, GlobalState globalState, FunctionState functionState, BlockState blockState) {
        if (instruction.getOpName().equals("call")) {
            String functionName = instruction.getArguments().get(instruction.getArguments().size() - 1).getName();
            if (SVCOMP_ERROR_FUNCTIONS.contains(functionName)) {
                error(instruction, globalState, functionState, blockState);
                return;
            }
        }
        super.handleInstruction(instruction, globalState, functionState, blockState);
    }

    private void error(Instruction instruction, GlobalState globalState, FunctionState functionState, BlockState blockState) {
        functionState.getProcedureBuilder().createErrorLoc();
        XcfaLocation newLoc = functionState.getProcedureBuilder().getErrorLoc().get();
        XcfaEdge edge = new XcfaEdge(blockState.getLastLocation(), newLoc, NopLabel.INSTANCE, new LlvmMetadata(instruction.getLineNumber()));
        functionState.getProcedureBuilder().addEdge(edge);
        blockState.setLastLocation(newLoc);
    }
}
