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

import hu.bme.mit.theta.common.Tuple2;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.stmt.Stmt;
import hu.bme.mit.theta.llvm2xcfa.LlvmMetadata;
import hu.bme.mit.theta.llvm2xcfa.Utils;
import hu.bme.mit.theta.llvm2xcfa.handlers.BaseInstructionHandler;
import hu.bme.mit.theta.llvm2xcfa.handlers.Instruction;
import hu.bme.mit.theta.llvm2xcfa.handlers.arguments.Argument;
import hu.bme.mit.theta.llvm2xcfa.handlers.arguments.RegArgument;
import hu.bme.mit.theta.llvm2xcfa.handlers.states.BlockState;
import hu.bme.mit.theta.llvm2xcfa.handlers.states.FunctionState;
import hu.bme.mit.theta.llvm2xcfa.handlers.states.GlobalState;
import hu.bme.mit.theta.xcfa.model.EmptyMetaData;
import hu.bme.mit.theta.xcfa.model.StmtLabel;
import hu.bme.mit.theta.xcfa.model.XcfaEdge;
import hu.bme.mit.theta.xcfa.model.XcfaLocation;

import java.util.Optional;

import static com.google.common.base.Preconditions.checkState;
import static hu.bme.mit.theta.core.decl.Decls.Var;
import static hu.bme.mit.theta.core.stmt.Stmts.Assign;
import static hu.bme.mit.theta.core.utils.TypeUtils.cast;
import static hu.bme.mit.theta.llvm2xcfa.Utils.foldExpression;

public class MemoryInstructionHandler extends BaseInstructionHandler {
    @Override
    public void handleInstruction(Instruction instruction, GlobalState globalState, FunctionState functionState, BlockState blockState) {
        switch (instruction.getOpName()) {
            case "alloca":
                alloca(instruction, globalState, functionState, blockState);
                break;
            case "load":
                load(instruction, globalState, functionState, blockState);
                break;
            case "store":
                store(instruction, globalState, functionState, blockState);
                break;
            case "getelementptr":
                getelementptr(instruction, globalState, functionState, blockState);
                break;
            case "fence":
            case "cmpxchg":
            case "atomicrmw":
                break;
            default:
                super.handleInstruction(instruction, globalState, functionState, blockState);
                break;
        }

    }

    private void load(Instruction instruction, GlobalState globalState, FunctionState functionState, BlockState blockState) {
        Argument isatomic = instruction.getArguments().get(0);
        Argument op;
        checkState(instruction.getRetVar().isPresent(), "Load must load into a variable");
        Argument ret = instruction.getRetVar().get();
        if (isatomic.getName().equals("atomic"))
            op = instruction.getArguments().get(2);
        else
            op = instruction.getArguments().get(1);
        checkState(functionState.getLocalVars().containsKey(op.getName()), "Load must load a variable!");

        foldExpression(instruction, functionState, blockState, op.getName(), Utils.getOrCreateVar(functionState, op).getRef(), 1);
    }

    private void store(Instruction instruction, GlobalState globalState, FunctionState functionState, BlockState blockState) {
        Argument isatomic = instruction.getArguments().get(0);
        Argument op1;
        Argument op2;
        if (isatomic.getName().equals("atomic")) {
            op1 = instruction.getArguments().get(2);
            op2 = instruction.getArguments().get(3);
        } else {
            op1 = instruction.getArguments().get(1);
            op2 = instruction.getArguments().get(2);
        }

        Tuple2<VarDecl<?>, Integer> oldVar = functionState.getLocalVars().get(op2.getName());
        Tuple2<VarDecl<?>, Integer> potentialParam = functionState.getLocalVars().get(op1.getName());
        checkState(functionState.getLocalVars().containsKey(op2.getName()) || functionState.getParams().contains(oldVar.get1()), "Store must store into a variable!");

        if (oldVar.get2() > 1) {
            functionState.getLocalVars().put(op2.getName(), Tuple2.of(oldVar.get1(), oldVar.get2() - 1));
        } else if (oldVar.get2() == 1) {
            if (potentialParam != null && functionState.getParams().contains(potentialParam.get1())) {
                VarDecl<?> var = functionState.getLocalVars().get(op2.getName()).get1();
                functionState.getProcedureBuilder().getVars().remove(var);
                var = functionState.getLocalVars().get(op1.getName()).get1();
                functionState.getLocalVars().put(op2.getName(), Tuple2.of(var, 0));
                functionState.getValues().put(op1.getName(), var.getRef());
                functionState.getValues().put(op2.getName(), var.getRef());
            } else {
                XcfaLocation loc = new XcfaLocation(blockState.getName() + "_" + blockState.getBlockCnt());
                VarDecl<?> var = functionState.getLocalVars().get(op2.getName()).get1();
                Stmt stmt = Assign(cast(var, var.getType()), cast(op1.getExpr(functionState.getValues()), var.getType()));
                XcfaEdge edge = new XcfaEdge(blockState.getLastLocation(), loc, new StmtLabel(stmt, EmptyMetaData.INSTANCE), new LlvmMetadata(instruction.getLineNumber()));
                functionState.getProcedureBuilder().addLoc(loc);
                functionState.getProcedureBuilder().addEdge(edge);
                blockState.setLastLocation(loc);
            }
        }

    }

    private void getelementptr(Instruction instruction, GlobalState globalState, FunctionState functionState, BlockState blockState) {
        throw new RuntimeException("Not yet implemented!");
    }

    private void alloca(Instruction instruction, GlobalState globalState, FunctionState functionState, BlockState blockState) {
        Optional<RegArgument> retVar = instruction.getRetVar();
        checkState(retVar.isPresent(), "Alloca must have a variable tied to it");
        VarDecl<?> var = Var(retVar.get().getName(), retVar.get().getType());
        functionState.getProcedureBuilder().getVars().add(var);
        functionState.getLocalVars().put(retVar.get().getName(), Tuple2.of(var, 1));
        functionState.getValues().put(retVar.get().getName(), var.getRef());
    }
}
