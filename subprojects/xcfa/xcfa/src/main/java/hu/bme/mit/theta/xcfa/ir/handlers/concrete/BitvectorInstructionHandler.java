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

import hu.bme.mit.theta.core.type.bvtype.BvExprs;
import hu.bme.mit.theta.core.type.bvtype.BvType;
import hu.bme.mit.theta.xcfa.ir.handlers.BaseInstructionHandler;
import hu.bme.mit.theta.xcfa.ir.handlers.Instruction;
import hu.bme.mit.theta.xcfa.ir.handlers.arguments.Argument;
import hu.bme.mit.theta.xcfa.ir.handlers.arguments.StringArgument;
import hu.bme.mit.theta.xcfa.ir.handlers.states.BlockState;
import hu.bme.mit.theta.xcfa.ir.handlers.states.FunctionState;
import hu.bme.mit.theta.xcfa.ir.handlers.states.GlobalState;

import java.util.List;

import static com.google.common.base.Preconditions.checkState;
import static hu.bme.mit.theta.core.utils.TypeUtils.cast;

public class BitvectorInstructionHandler extends BaseInstructionHandler {
    @Override
    public void handleInstruction(Instruction instruction, GlobalState globalState, FunctionState functionState, BlockState blockState) {
        switch (instruction.getOpName()) {
            case "icmp":
                icmp(instruction, globalState, functionState, blockState);
                break;
            case "shl":
                shl(instruction, globalState, functionState, blockState);
                break;
            case "lshr":
                lshr(instruction, globalState, functionState, blockState);
                break;
            case "ashr":
                ashr(instruction, globalState, functionState, blockState);
                break;
            case "and":
                and(instruction, globalState, functionState, blockState);
                break;
            case "or":
                or(instruction, globalState, functionState, blockState);
                break;
            case "xor":
                xor(instruction, globalState, functionState, blockState);
                break;
            case "add":
                add(instruction, globalState, functionState, blockState);
                break;
            case "sub":
                sub(instruction, globalState, functionState, blockState);
                break;
            case "mul":
                mul(instruction, globalState, functionState, blockState);
                break;
            case "udiv":
                udiv(instruction, globalState, functionState, blockState);
            case "sdiv":
                sdiv(instruction, globalState, functionState, blockState);
                break;
            case "urem":
                urem(instruction, globalState, functionState, blockState);
            case "srem":
                srem(instruction, globalState, functionState, blockState);
                break;
            default:
                super.handleInstruction(instruction, globalState, functionState, blockState);
                break;
        }

    }


    private void icmp(Instruction instruction, GlobalState globalState, FunctionState functionState, BlockState blockState) {
        Argument op1 = instruction.getArguments().get(0);
        Argument op2 = instruction.getArguments().get(1);
        Argument op3 = instruction.getArguments().get(2);

        checkState(op1 instanceof StringArgument, "Icmp has to have string argument as first operand!");
        checkState(op2.getType() instanceof BvType, "Bitvector Icmp only supports bitvector types!");
        checkState(op3.getType() instanceof BvType, "Bitvector Icmp only supports bitvector types!");
        checkState(instruction.getRetVar().isPresent(), "Instruction must have return variable");
        switch (op1.getName()) {
            case "eq":
                functionState.getValues().put(instruction.getRetVar().get().getName(), BvExprs.Eq(cast(op2.getExpr(functionState.getValues()), (BvType)op2.getType()), cast(op3.getExpr(functionState.getValues()), (BvType)op2.getType())));
                break;
            case "ne":
                functionState.getValues().put(instruction.getRetVar().get().getName(), BvExprs.Neq(cast(op2.getExpr(functionState.getValues()), (BvType)op2.getType()), cast(op3.getExpr(functionState.getValues()), (BvType)op2.getType())));
                break;
            case "ugt":
                functionState.getValues().put(instruction.getRetVar().get().getName(), BvExprs.UGt(cast(op2.getExpr(functionState.getValues()), (BvType)op2.getType()), cast(op3.getExpr(functionState.getValues()), (BvType)op2.getType())));
                break;
            case "sgt":
                functionState.getValues().put(instruction.getRetVar().get().getName(), BvExprs.SGt(cast(op2.getExpr(functionState.getValues()), (BvType)op2.getType()), cast(op3.getExpr(functionState.getValues()), (BvType)op2.getType())));
                break;
            case "uge":
                functionState.getValues().put(instruction.getRetVar().get().getName(), BvExprs.UGeq(cast(op2.getExpr(functionState.getValues()), (BvType)op2.getType()), cast(op3.getExpr(functionState.getValues()), (BvType)op2.getType())));
                break;
            case "sge":
                functionState.getValues().put(instruction.getRetVar().get().getName(), BvExprs.SGeq(cast(op2.getExpr(functionState.getValues()), (BvType)op2.getType()), cast(op3.getExpr(functionState.getValues()), (BvType)op2.getType())));
                break;
            case "ult":
                functionState.getValues().put(instruction.getRetVar().get().getName(), BvExprs.ULt(cast(op2.getExpr(functionState.getValues()), (BvType)op2.getType()), cast(op3.getExpr(functionState.getValues()), (BvType)op2.getType())));
                break;
            case "slt":
                functionState.getValues().put(instruction.getRetVar().get().getName(), BvExprs.SLt(cast(op2.getExpr(functionState.getValues()), (BvType)op2.getType()), cast(op3.getExpr(functionState.getValues()), (BvType)op2.getType())));
                break;
            case "ule":
                functionState.getValues().put(instruction.getRetVar().get().getName(), BvExprs.ULeq(cast(op2.getExpr(functionState.getValues()), (BvType)op2.getType()), cast(op3.getExpr(functionState.getValues()), (BvType)op2.getType())));
                break;
            case "sle":
                functionState.getValues().put(instruction.getRetVar().get().getName(), BvExprs.SLeq(cast(op2.getExpr(functionState.getValues()), (BvType)op2.getType()), cast(op3.getExpr(functionState.getValues()), (BvType)op2.getType())));
                break;
            default:
                throw new IllegalStateException("Unexpected value: " + op1.getName());
        }
    }

    private void urem(Instruction instruction, GlobalState globalState, FunctionState functionState, BlockState blockState) {
        Argument op1 = instruction.getArguments().get(0);
        Argument op2 = instruction.getArguments().get(1);

        checkState(op1.getType() instanceof BvType, "Bitvector instructions only supports bitvector types!");
        checkState(op2.getType() instanceof BvType, "Bitvector instructions only supports bitvector types!");
        checkState(instruction.getRetVar().isPresent(), "Instruction must have return variable");
        functionState.getValues().put(instruction.getRetVar().get().getName(), BvExprs.URem(cast(op1.getExpr(functionState.getValues()), (BvType)op2.getType()), cast(op2.getExpr(functionState.getValues()), (BvType)op2.getType())));
    }

    private void srem(Instruction instruction, GlobalState globalState, FunctionState functionState, BlockState blockState) {
        Argument op1 = instruction.getArguments().get(0);
        Argument op2 = instruction.getArguments().get(1);

        checkState(op1.getType() instanceof BvType, "Bitvector instructions only supports bitvector types!");
        checkState(op2.getType() instanceof BvType, "Bitvector instructions only supports bitvector types!");
        checkState(instruction.getRetVar().isPresent(), "Instruction must have return variable");
        functionState.getValues().put(instruction.getRetVar().get().getName(), BvExprs.SRem(cast(op1.getExpr(functionState.getValues()), (BvType)op2.getType()), cast(op2.getExpr(functionState.getValues()), (BvType)op2.getType())));
    }

    private void udiv(Instruction instruction, GlobalState globalState, FunctionState functionState, BlockState blockState) {
        Argument op1 = instruction.getArguments().get(0);
        Argument op2 = instruction.getArguments().get(1);

        checkState(op1.getType() instanceof BvType, "Bitvector instructions only supports bitvector types!");
        checkState(op2.getType() instanceof BvType, "Bitvector instructions only supports bitvector types!");
        checkState(instruction.getRetVar().isPresent(), "Instruction must have return variable");
        functionState.getValues().put(instruction.getRetVar().get().getName(), BvExprs.UDiv(cast(op1.getExpr(functionState.getValues()), (BvType)op2.getType()), cast(op2.getExpr(functionState.getValues()), (BvType)op2.getType())));
    }

    private void sdiv(Instruction instruction, GlobalState globalState, FunctionState functionState, BlockState blockState) {
        Argument op1 = instruction.getArguments().get(0);
        Argument op2 = instruction.getArguments().get(1);

        checkState(op1.getType() instanceof BvType, "Bitvector instructions only supports bitvector types!");
        checkState(op2.getType() instanceof BvType, "Bitvector instructions only supports bitvector types!");
        checkState(instruction.getRetVar().isPresent(), "Instruction must have return variable");
        functionState.getValues().put(instruction.getRetVar().get().getName(), BvExprs.SDiv(cast(op1.getExpr(functionState.getValues()), (BvType)op2.getType()), cast(op2.getExpr(functionState.getValues()), (BvType)op2.getType())));
    }

    private void mul(Instruction instruction, GlobalState globalState, FunctionState functionState, BlockState blockState) {
        Argument op1 = instruction.getArguments().get(0);
        Argument op2 = instruction.getArguments().get(1);

        checkState(op1.getType() instanceof BvType, "Bitvector instructions only supports bitvector types!");
        checkState(op2.getType() instanceof BvType, "Bitvector instructions only supports bitvector types!");
        checkState(instruction.getRetVar().isPresent(), "Instruction must have return variable");
        functionState.getValues().put(instruction.getRetVar().get().getName(), BvExprs.Mul(List.of(cast(op1.getExpr(functionState.getValues()), (BvType)op2.getType()), cast(op2.getExpr(functionState.getValues()), (BvType)op2.getType()))));
    }

    private void sub(Instruction instruction, GlobalState globalState, FunctionState functionState, BlockState blockState) {
        Argument op1 = instruction.getArguments().get(0);
        Argument op2 = instruction.getArguments().get(1);

        checkState(op1.getType() instanceof BvType, "Bitvector instructions only supports bitvector types!");
        checkState(op2.getType() instanceof BvType, "Bitvector instructions only supports bitvector types!");
        checkState(instruction.getRetVar().isPresent(), "Instruction must have return variable");
        functionState.getValues().put(instruction.getRetVar().get().getName(), BvExprs.Sub(cast(op1.getExpr(functionState.getValues()), (BvType)op2.getType()), cast(op2.getExpr(functionState.getValues()), (BvType)op2.getType())));
    }

    private void add(Instruction instruction, GlobalState globalState, FunctionState functionState, BlockState blockState) {
        Argument op1 = instruction.getArguments().get(0);
        Argument op2 = instruction.getArguments().get(1);

        checkState(op1.getType() instanceof BvType, "Bitvector instructions only supports bitvector types!");
        checkState(op2.getType() instanceof BvType, "Bitvector instructions only supports bitvector types!");
        checkState(instruction.getRetVar().isPresent(), "Instruction must have return variable");
        functionState.getValues().put(instruction.getRetVar().get().getName(), BvExprs.Add(List.of(cast(op1.getExpr(functionState.getValues()), (BvType)op2.getType()), cast(op2.getExpr(functionState.getValues()), (BvType)op2.getType()))));
    }

    private void shl(Instruction instruction, GlobalState globalState, FunctionState functionState, BlockState blockState) {
        Argument op1 = instruction.getArguments().get(0);
        Argument op2 = instruction.getArguments().get(1);

        checkState(op1.getType() instanceof BvType, "Bitvector instructions only supports bitvector types!");
        checkState(op2.getType() instanceof BvType, "Bitvector instructions only supports bitvector types!");
        checkState(instruction.getRetVar().isPresent(), "Instruction must have return variable");
        functionState.getValues().put(instruction.getRetVar().get().getName(), BvExprs.ShiftLeft(cast(op1.getExpr(functionState.getValues()), (BvType)op2.getType()), cast(op2.getExpr(functionState.getValues()), (BvType)op2.getType())));

    }

    private void lshr(Instruction instruction, GlobalState globalState, FunctionState functionState, BlockState blockState) {
        Argument op1 = instruction.getArguments().get(0);
        Argument op2 = instruction.getArguments().get(1);

        checkState(op1.getType() instanceof BvType, "Bitvector instructions only supports bitvector types!");
        checkState(op2.getType() instanceof BvType, "Bitvector instructions only supports bitvector types!");
        checkState(instruction.getRetVar().isPresent(), "Instruction must have return variable");
        functionState.getValues().put(instruction.getRetVar().get().getName(), BvExprs.LogicShiftRight(cast(op1.getExpr(functionState.getValues()), (BvType)op2.getType()), cast(op2.getExpr(functionState.getValues()), (BvType)op2.getType())));

    }

    private void ashr(Instruction instruction, GlobalState globalState, FunctionState functionState, BlockState blockState) {
        Argument op1 = instruction.getArguments().get(0);
        Argument op2 = instruction.getArguments().get(1);

        checkState(op1.getType() instanceof BvType, "Bitvector instructions only supports bitvector types!");
        checkState(op2.getType() instanceof BvType, "Bitvector instructions only supports bitvector types!");
        checkState(instruction.getRetVar().isPresent(), "Instruction must have return variable");
        functionState.getValues().put(instruction.getRetVar().get().getName(), BvExprs.ArithShiftRight(cast(op1.getExpr(functionState.getValues()), (BvType)op2.getType()), cast(op2.getExpr(functionState.getValues()), (BvType)op2.getType())));

    }

    private void and(Instruction instruction, GlobalState globalState, FunctionState functionState, BlockState blockState) {
        Argument op1 = instruction.getArguments().get(0);
        Argument op2 = instruction.getArguments().get(1);

        checkState(op1.getType() instanceof BvType, "Bitvector instructions only supports bitvector types!");
        checkState(op2.getType() instanceof BvType, "Bitvector instructions only supports bitvector types!");
        checkState(instruction.getRetVar().isPresent(), "Instruction must have return variable");
        functionState.getValues().put(instruction.getRetVar().get().getName(), BvExprs.And(List.of(cast(op1.getExpr(functionState.getValues()), (BvType)op2.getType()), cast(op2.getExpr(functionState.getValues()), (BvType)op2.getType()))));
    }

    private void or(Instruction instruction, GlobalState globalState, FunctionState functionState, BlockState blockState) {
        Argument op1 = instruction.getArguments().get(0);
        Argument op2 = instruction.getArguments().get(1);

        checkState(op1.getType() instanceof BvType, "Bitvector instructions only supports bitvector types!");
        checkState(op2.getType() instanceof BvType, "Bitvector instructions only supports bitvector types!");
        checkState(instruction.getRetVar().isPresent(), "Instruction must have return variable");
        functionState.getValues().put(instruction.getRetVar().get().getName(), BvExprs.Or(List.of(cast(op1.getExpr(functionState.getValues()), (BvType)op2.getType()), cast(op2.getExpr(functionState.getValues()), (BvType)op2.getType()))));
    }

    private void xor(Instruction instruction, GlobalState globalState, FunctionState functionState, BlockState blockState) {
        Argument op1 = instruction.getArguments().get(0);
        Argument op2 = instruction.getArguments().get(1);

        checkState(op1.getType() instanceof BvType, "Bitvector instructions only supports bitvector types!");
        checkState(op2.getType() instanceof BvType, "Bitvector instructions only supports bitvector types!");
        checkState(instruction.getRetVar().isPresent(), "Instruction must have return variable");
        functionState.getValues().put(instruction.getRetVar().get().getName(), BvExprs.Xor(List.of(cast(op1.getExpr(functionState.getValues()), (BvType)op2.getType()), cast(op2.getExpr(functionState.getValues()), (BvType)op2.getType()))));

    }
}
