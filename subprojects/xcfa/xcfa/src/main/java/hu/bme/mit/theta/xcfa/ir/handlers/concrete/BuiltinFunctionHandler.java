/*
 * Copyright 2021 Budapest University of Technology and Economics
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package hu.bme.mit.theta.xcfa.ir.handlers.concrete;

import hu.bme.mit.theta.frontend.FrontendMetadata;
import hu.bme.mit.theta.xcfa.model.XcfaEdge;
import hu.bme.mit.theta.xcfa.model.XcfaLocation;
import hu.bme.mit.theta.xcfa.ir.handlers.BaseInstructionHandler;
import hu.bme.mit.theta.xcfa.ir.handlers.Instruction;
import hu.bme.mit.theta.xcfa.ir.handlers.states.BlockState;
import hu.bme.mit.theta.xcfa.ir.handlers.states.FunctionState;
import hu.bme.mit.theta.xcfa.ir.handlers.states.GlobalState;

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
        XcfaLocation newLoc = XcfaLocation.create(blockState.getName() + "_" + blockState.getBlockCnt());
        XcfaEdge edge = XcfaEdge.create(blockState.getLastLocation(), newLoc, List.of());
        if (instruction.getLineNumber() >= 0) FrontendMetadata.create(edge, "lineNumber", instruction.getLineNumber());
        functionState.getProcedureBuilder().addLoc(newLoc);
        functionState.getProcedureBuilder().addEdge(edge);
        blockState.setLastLocation(newLoc);
        functionState.getProcedureBuilder().setErrorLoc(newLoc);
    }
}
