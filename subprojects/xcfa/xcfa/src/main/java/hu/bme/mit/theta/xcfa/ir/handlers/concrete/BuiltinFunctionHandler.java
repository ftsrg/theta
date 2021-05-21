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

import hu.bme.mit.theta.core.stmt.xcfa.AtomicBeginStmt;
import hu.bme.mit.theta.core.stmt.xcfa.AtomicEndStmt;
import hu.bme.mit.theta.core.stmt.xcfa.JoinThreadStmt;
import hu.bme.mit.theta.core.stmt.xcfa.StartThreadStmt;
import hu.bme.mit.theta.core.stmt.xcfa.StoreStmt;
import hu.bme.mit.theta.xcfa.ir.handlers.BaseInstructionHandler;
import hu.bme.mit.theta.xcfa.ir.handlers.Instruction;
import hu.bme.mit.theta.xcfa.ir.handlers.arguments.Argument;
import hu.bme.mit.theta.xcfa.ir.handlers.arguments.RegArgument;
import hu.bme.mit.theta.xcfa.ir.handlers.states.BlockState;
import hu.bme.mit.theta.xcfa.ir.handlers.states.FunctionState;
import hu.bme.mit.theta.xcfa.ir.handlers.states.GlobalState;
import hu.bme.mit.theta.xcfa.model.XcfaEdge;
import hu.bme.mit.theta.xcfa.model.XcfaLocation;
import hu.bme.mit.theta.xcfa.model.XcfaMetadata;

import java.util.Collection;
import java.util.HashMap;
import java.util.List;
import java.util.Optional;

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
            } else if (SVCOMP_NEWTHREAD_FUNCTIONS.contains(functionName)) {
                newthread(instruction, globalState, functionState, blockState);
                return;
            } else if (SVCOMP_JOINTHREAD_FUNCTIONS.contains(functionName)) {
                jointhread(instruction, globalState, functionState, blockState);
                return;
            } else if (SVCOMP_ATOMIC_BEGIN.contains(functionName)) {
                atomicbegin(instruction, globalState, functionState, blockState);
                return;
            } else if (SVCOMP_ATOMIC_END.contains(functionName)) {
                atomicend(instruction, globalState, functionState, blockState);
                return;
            } else if (ATOMIC_READ.contains(functionName)) {
                atomicread(instruction, globalState, functionState, blockState);
                return;
            } else if (ATOMIC_WRITE.contains(functionName)) {
                atomicwrite(instruction, globalState, functionState, blockState);
                return;
            }
        }
        super.handleInstruction(instruction, globalState, functionState, blockState);
    }

    private void error(Instruction instruction, GlobalState globalState, FunctionState functionState, BlockState blockState) {
        XcfaLocation newLoc = new XcfaLocation(blockState.getName() + "_" + blockState.getBlockCnt(), new HashMap<>());
        XcfaEdge edge = new XcfaEdge(blockState.getLastLocation(), newLoc, List.of());
        if (instruction.getLineNumber() >= 0) XcfaMetadata.create(edge, "lineNumber", instruction.getLineNumber());
        functionState.getProcedureBuilder().addLoc(newLoc);
        functionState.getProcedureBuilder().addEdge(edge);
        blockState.setLastLocation(newLoc);
        functionState.getProcedureBuilder().setErrorLoc(newLoc);
    }

    private void newthread(Instruction instruction, GlobalState globalState, FunctionState functionState, BlockState blockState) {
        XcfaLocation newLoc = new XcfaLocation(blockState.getName() + "_" + blockState.getBlockCnt(), new HashMap<>());
        Argument handleName = instruction.getArguments().get(0);
        Argument functionName = instruction.getArguments().get(1);
        Argument param = instruction.getArguments().get(2);
        XcfaEdge edge = new XcfaEdge(blockState.getLastLocation(), newLoc, List.of(new StartThreadStmt(handleName.getName(), functionName.getName(), param.getExpr(functionState.getValues()))));
        if (instruction.getLineNumber() >= 0) XcfaMetadata.create(edge, "lineNumber", instruction.getLineNumber());
        functionState.getProcedureBuilder().addLoc(newLoc);
        functionState.getProcedureBuilder().addEdge(edge);
        blockState.setLastLocation(newLoc);
    }

    private void jointhread(Instruction instruction, GlobalState globalState, FunctionState functionState, BlockState blockState) {
        XcfaLocation newLoc = new XcfaLocation(blockState.getName() + "_" + blockState.getBlockCnt(), new HashMap<>());
        Argument handleName = instruction.getArguments().get(0);
        XcfaEdge edge = new XcfaEdge(blockState.getLastLocation(), newLoc, List.of(new JoinThreadStmt(handleName.getName())));
        if (instruction.getLineNumber() >= 0) XcfaMetadata.create(edge, "lineNumber", instruction.getLineNumber());
        functionState.getProcedureBuilder().addLoc(newLoc);
        functionState.getProcedureBuilder().addEdge(edge);
        blockState.setLastLocation(newLoc);
    }

    private void atomicbegin(Instruction instruction, GlobalState globalState, FunctionState functionState, BlockState blockState) {
        XcfaLocation newLoc = new XcfaLocation(blockState.getName() + "_" + blockState.getBlockCnt(), new HashMap<>());
        XcfaEdge edge = new XcfaEdge(blockState.getLastLocation(), newLoc, List.of(new AtomicBeginStmt()));
        if (instruction.getLineNumber() >= 0) XcfaMetadata.create(edge, "lineNumber", instruction.getLineNumber());
        functionState.getProcedureBuilder().addLoc(newLoc);
        functionState.getProcedureBuilder().addEdge(edge);
        blockState.setLastLocation(newLoc);
    }

    private void atomicend(Instruction instruction, GlobalState globalState, FunctionState functionState, BlockState blockState) {
        XcfaLocation newLoc = new XcfaLocation(blockState.getName() + "_" + blockState.getBlockCnt(), new HashMap<>());
        XcfaEdge edge = new XcfaEdge(blockState.getLastLocation(), newLoc, List.of(new AtomicEndStmt()));
        if (instruction.getLineNumber() >= 0) XcfaMetadata.create(edge, "lineNumber", instruction.getLineNumber());
        functionState.getProcedureBuilder().addLoc(newLoc);
        functionState.getProcedureBuilder().addEdge(edge);
        blockState.setLastLocation(newLoc);
    }
    private void atomicwrite(Instruction instruction, GlobalState globalState, FunctionState functionState, BlockState blockState) {
        XcfaLocation newLoc = new XcfaLocation(blockState.getName() + "_" + blockState.getBlockCnt(), new HashMap<>());
        XcfaEdge edge = new XcfaEdge(blockState.getLastLocation(), newLoc, List.of());
        if (instruction.getLineNumber() >= 0) XcfaMetadata.create(edge, "lineNumber", instruction.getLineNumber());
        functionState.getProcedureBuilder().addLoc(newLoc);
        functionState.getProcedureBuilder().addEdge(edge);
        blockState.setLastLocation(newLoc);
    }
    private void atomicread(Instruction instruction, GlobalState globalState, FunctionState functionState, BlockState blockState) {
        XcfaLocation newLoc = new XcfaLocation(blockState.getName() + "_" + blockState.getBlockCnt(), new HashMap<>());
        XcfaEdge edge = new XcfaEdge(blockState.getLastLocation(), newLoc, List.of(new AtomicEndStmt()));
        if (instruction.getLineNumber() >= 0) XcfaMetadata.create(edge, "lineNumber", instruction.getLineNumber());
        functionState.getProcedureBuilder().addLoc(newLoc);
        functionState.getProcedureBuilder().addEdge(edge);
        blockState.setLastLocation(newLoc);
    }
}
