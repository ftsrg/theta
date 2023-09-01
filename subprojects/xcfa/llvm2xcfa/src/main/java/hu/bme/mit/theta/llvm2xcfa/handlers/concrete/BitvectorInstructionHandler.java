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

import hu.bme.mit.theta.core.type.booltype.BoolExprs;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.type.bvtype.BvExprs;
import hu.bme.mit.theta.core.type.bvtype.BvType;
import hu.bme.mit.theta.core.type.inttype.IntLitExpr;
import hu.bme.mit.theta.llvm2xcfa.handlers.BaseInstructionHandler;
import hu.bme.mit.theta.llvm2xcfa.handlers.Instruction;
import hu.bme.mit.theta.llvm2xcfa.handlers.arguments.Argument;
import hu.bme.mit.theta.llvm2xcfa.handlers.arguments.StringArgument;
import hu.bme.mit.theta.llvm2xcfa.handlers.states.BlockState;
import hu.bme.mit.theta.llvm2xcfa.handlers.states.FunctionState;
import hu.bme.mit.theta.llvm2xcfa.handlers.states.GlobalState;

import java.math.BigInteger;
import java.util.List;

import static com.google.common.base.Preconditions.checkState;
import static hu.bme.mit.theta.core.utils.TypeUtils.cast;
import static hu.bme.mit.theta.llvm2xcfa.Utils.foldExpression;

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
                break;
            case "sdiv":
                sdiv(instruction, globalState, functionState, blockState);
                break;
            case "urem":
                urem(instruction, globalState, functionState, blockState);
                break;
            case "srem":
                srem(instruction, globalState, functionState, blockState);
                break;
            case "trunc":
                trunc(instruction, globalState, functionState, blockState);
                break;
            case "zext":
                zext(instruction, globalState, functionState, blockState);
                break;
            case "sext":
                sext(instruction, globalState, functionState, blockState);
                break;
            case "fptoui":
                fptoui(instruction, globalState, functionState, blockState);
                break;
            case "fptosi":
                fptosi(instruction, globalState, functionState, blockState);
                break;
            case "uitofp":
                uitofp(instruction, globalState, functionState, blockState);
                break;
            case "sitofp":
                sitofp(instruction, globalState, functionState, blockState);
                break;
            case "bitcast":
                bitcast(instruction, globalState, functionState, blockState);
                break;
            default:
                super.handleInstruction(instruction, globalState, functionState, blockState);
                break;
        }

    }

    private void trunc(Instruction instruction, GlobalState globalState, FunctionState functionState, BlockState blockState) {
        Argument op1 = instruction.getArguments().get(0);

        checkState(op1.getType() instanceof BvType, "Bitvector instructions only supports bitvector types!");
        checkState(instruction.getRetVar().isPresent(), "Instruction must have return variable");
        BigInteger newSize = BigInteger.valueOf(((BvType) instruction.getRetVar().get().getType()).getSize());
        BigInteger oldSize = BigInteger.valueOf(((BvType) op1.getType()).getSize());
        foldExpression(instruction, functionState, blockState, null, BvExprs.Extract(cast(op1.getExpr(functionState.getValues()), (BvType) op1.getType()), IntLitExpr.of(oldSize.subtract(newSize)), IntLitExpr.of(oldSize)), 0);
    }

    private void zext(Instruction instruction, GlobalState globalState, FunctionState functionState, BlockState blockState) {
        Argument op1 = instruction.getArguments().get(0);

        checkState(op1.getType() instanceof BvType, "Bitvector instructions only supports bitvector types!");
        checkState(instruction.getRetVar().isPresent(), "Instruction must have return variable");
        //TODO: bool exprs?
        foldExpression(instruction, functionState, blockState, null, BvExprs.ZExt(cast(op1.getExpr(functionState.getValues()), (BvType) op1.getType()), (BvType) instruction.getRetVar().get().getType()), 0);
    }

    private void sext(Instruction instruction, GlobalState globalState, FunctionState functionState, BlockState blockState) {
        Argument op1 = instruction.getArguments().get(0);

        checkState(op1.getType() instanceof BvType, "Bitvector instructions only supports bitvector types!");
        checkState(instruction.getRetVar().isPresent(), "Instruction must have return variable");
        foldExpression(instruction, functionState, blockState, null, BvExprs.SExt(cast(op1.getExpr(functionState.getValues()), (BvType) op1.getType()), (BvType) instruction.getRetVar().get().getType()), 0);
    }

    private void fptoui(Instruction instruction, GlobalState globalState, FunctionState functionState, BlockState blockState) {
        throw new RuntimeException("Not yet implemented!");
    }

    private void fptosi(Instruction instruction, GlobalState globalState, FunctionState functionState, BlockState blockState) {
        throw new RuntimeException("Not yet implemented!");
    }

    private void uitofp(Instruction instruction, GlobalState globalState, FunctionState functionState, BlockState blockState) {
        throw new RuntimeException("Not yet implemented!");
    }

    private void sitofp(Instruction instruction, GlobalState globalState, FunctionState functionState, BlockState blockState) {
        throw new RuntimeException("Not yet implemented!");
    }

    private void bitcast(Instruction instruction, GlobalState globalState, FunctionState functionState, BlockState blockState) {
        Argument op1 = instruction.getArguments().get(0);

        checkState(op1.getType() instanceof BvType, "Bitvector instructions only supports bitvector types!");
        checkState(instruction.getRetVar().isPresent(), "Instruction must have return variable");
        BigInteger newSize = BigInteger.valueOf(((BvType) instruction.getRetVar().get().getType()).getSize());
        BigInteger oldSize = BigInteger.valueOf(((BvType) op1.getType()).getSize());
        if (newSize.subtract(oldSize).signum() == 1) {
            zext(instruction, globalState, functionState, blockState);
        } else {
            trunc(instruction, globalState, functionState, blockState);
        }
        if (functionState.getLocalVars().containsKey(op1.getName())) {
            functionState.getLocalVars().put(instruction.getRetVar().get().getName(), functionState.getLocalVars().get(op1.getName()));
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
                foldExpression(instruction, functionState, blockState, null, BvExprs.Eq(cast(op2.getExpr(functionState.getValues()), (BvType) op2.getType()), cast(op3.getExpr(functionState.getValues()), (BvType) op2.getType())), 0);
                break;
            case "ne":
                foldExpression(instruction, functionState, blockState, null, BvExprs.Neq(cast(op2.getExpr(functionState.getValues()), (BvType) op2.getType()), cast(op3.getExpr(functionState.getValues()), (BvType) op2.getType())), 0);
                break;
            case "ugt":
                foldExpression(instruction, functionState, blockState, null, BvExprs.UGt(cast(op2.getExpr(functionState.getValues()), (BvType) op2.getType()), cast(op3.getExpr(functionState.getValues()), (BvType) op2.getType())), 0);
                break;
            case "sgt":
                foldExpression(instruction, functionState, blockState, null, BvExprs.SGt(cast(op2.getExpr(functionState.getValues()), (BvType) op2.getType()), cast(op3.getExpr(functionState.getValues()), (BvType) op2.getType())), 0);
                break;
            case "uge":
                foldExpression(instruction, functionState, blockState, null, BvExprs.UGeq(cast(op2.getExpr(functionState.getValues()), (BvType) op2.getType()), cast(op3.getExpr(functionState.getValues()), (BvType) op2.getType())), 0);
                break;
            case "sge":
                foldExpression(instruction, functionState, blockState, null, BvExprs.SGeq(cast(op2.getExpr(functionState.getValues()), (BvType) op2.getType()), cast(op3.getExpr(functionState.getValues()), (BvType) op2.getType())), 0);
                break;
            case "ult":
                foldExpression(instruction, functionState, blockState, null, BvExprs.ULt(cast(op2.getExpr(functionState.getValues()), (BvType) op2.getType()), cast(op3.getExpr(functionState.getValues()), (BvType) op2.getType())), 0);
                break;
            case "slt":
                foldExpression(instruction, functionState, blockState, null, BvExprs.SLt(cast(op2.getExpr(functionState.getValues()), (BvType) op2.getType()), cast(op3.getExpr(functionState.getValues()), (BvType) op2.getType())), 0);
                break;
            case "ule":
                foldExpression(instruction, functionState, blockState, null, BvExprs.ULeq(cast(op2.getExpr(functionState.getValues()), (BvType) op2.getType()), cast(op3.getExpr(functionState.getValues()), (BvType) op2.getType())), 0);
                break;
            case "sle":
                foldExpression(instruction, functionState, blockState, null, BvExprs.SLeq(cast(op2.getExpr(functionState.getValues()), (BvType) op2.getType()), cast(op3.getExpr(functionState.getValues()), (BvType) op2.getType())), 0);
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
        foldExpression(instruction, functionState, blockState, null, BvExprs.URem(cast(op1.getExpr(functionState.getValues()), (BvType) op2.getType()), cast(op2.getExpr(functionState.getValues()), (BvType) op2.getType())), 0);
    }

    private void srem(Instruction instruction, GlobalState globalState, FunctionState functionState, BlockState blockState) {
        Argument op1 = instruction.getArguments().get(0);
        Argument op2 = instruction.getArguments().get(1);

        checkState(op1.getType() instanceof BvType, "Bitvector instructions only supports bitvector types!");
        checkState(op2.getType() instanceof BvType, "Bitvector instructions only supports bitvector types!");
        checkState(instruction.getRetVar().isPresent(), "Instruction must have return variable");
        foldExpression(instruction, functionState, blockState, null, BvExprs.SRem(cast(op1.getExpr(functionState.getValues()), (BvType) op2.getType()), cast(op2.getExpr(functionState.getValues()), (BvType) op2.getType())), 0);
    }

    private void udiv(Instruction instruction, GlobalState globalState, FunctionState functionState, BlockState blockState) {
        Argument op1 = instruction.getArguments().get(0);
        Argument op2 = instruction.getArguments().get(1);

        checkState(op1.getType() instanceof BvType, "Bitvector instructions only supports bitvector types!");
        checkState(op2.getType() instanceof BvType, "Bitvector instructions only supports bitvector types!");
        checkState(instruction.getRetVar().isPresent(), "Instruction must have return variable");
        foldExpression(instruction, functionState, blockState, null, BvExprs.UDiv(cast(op1.getExpr(functionState.getValues()), (BvType) op2.getType()), cast(op2.getExpr(functionState.getValues()), (BvType) op2.getType())), 0);
    }

    private void sdiv(Instruction instruction, GlobalState globalState, FunctionState functionState, BlockState blockState) {
        Argument op1 = instruction.getArguments().get(0);
        Argument op2 = instruction.getArguments().get(1);

        checkState(op1.getType() instanceof BvType, "Bitvector instructions only supports bitvector types!");
        checkState(op2.getType() instanceof BvType, "Bitvector instructions only supports bitvector types!");
        checkState(instruction.getRetVar().isPresent(), "Instruction must have return variable");
        foldExpression(instruction, functionState, blockState, null, BvExprs.SDiv(cast(op1.getExpr(functionState.getValues()), (BvType) op2.getType()), cast(op2.getExpr(functionState.getValues()), (BvType) op2.getType())), 0);
    }

    private void mul(Instruction instruction, GlobalState globalState, FunctionState functionState, BlockState blockState) {
        Argument op1 = instruction.getArguments().get(0);
        Argument op2 = instruction.getArguments().get(1);

        checkState(op1.getType() instanceof BvType, "Bitvector instructions only supports bitvector types!");
        checkState(op2.getType() instanceof BvType, "Bitvector instructions only supports bitvector types!");
        checkState(instruction.getRetVar().isPresent(), "Instruction must have return variable");
        foldExpression(instruction, functionState, blockState, null, BvExprs.Mul(List.of(cast(op1.getExpr(functionState.getValues()), (BvType) op2.getType()), cast(op2.getExpr(functionState.getValues()), (BvType) op2.getType()))), 0);
    }

    private void sub(Instruction instruction, GlobalState globalState, FunctionState functionState, BlockState blockState) {
        Argument op1 = instruction.getArguments().get(0);
        Argument op2 = instruction.getArguments().get(1);

        checkState(op1.getType() instanceof BvType, "Bitvector instructions only supports bitvector types!");
        checkState(op2.getType() instanceof BvType, "Bitvector instructions only supports bitvector types!");
        checkState(instruction.getRetVar().isPresent(), "Instruction must have return variable");
        foldExpression(instruction, functionState, blockState, null, BvExprs.Sub(cast(op1.getExpr(functionState.getValues()), (BvType) op2.getType()), cast(op2.getExpr(functionState.getValues()), (BvType) op2.getType())), 0);
    }

    private void add(Instruction instruction, GlobalState globalState, FunctionState functionState, BlockState blockState) {
        Argument op1 = instruction.getArguments().get(0);
        Argument op2 = instruction.getArguments().get(1);

        checkState(op1.getType() instanceof BvType, "Bitvector instructions only supports bitvector types!");
        checkState(op2.getType() instanceof BvType, "Bitvector instructions only supports bitvector types!");
        checkState(instruction.getRetVar().isPresent(), "Instruction must have return variable");
        foldExpression(instruction, functionState, blockState, null, BvExprs.Add(List.of(cast(op1.getExpr(functionState.getValues()), (BvType) op2.getType()), cast(op2.getExpr(functionState.getValues()), (BvType) op2.getType()))), 0);
    }

    private void shl(Instruction instruction, GlobalState globalState, FunctionState functionState, BlockState blockState) {
        Argument op1 = instruction.getArguments().get(0);
        Argument op2 = instruction.getArguments().get(1);

        checkState(op1.getType() instanceof BvType, "Bitvector instructions only supports bitvector types!");
        checkState(op2.getType() instanceof BvType, "Bitvector instructions only supports bitvector types!");
        checkState(instruction.getRetVar().isPresent(), "Instruction must have return variable");
        foldExpression(instruction, functionState, blockState, null, BvExprs.ShiftLeft(cast(op1.getExpr(functionState.getValues()), (BvType) op2.getType()), cast(op2.getExpr(functionState.getValues()), (BvType) op2.getType())), 0);

    }

    private void lshr(Instruction instruction, GlobalState globalState, FunctionState functionState, BlockState blockState) {
        Argument op1 = instruction.getArguments().get(0);
        Argument op2 = instruction.getArguments().get(1);

        checkState(op1.getType() instanceof BvType, "Bitvector instructions only supports bitvector types!");
        checkState(op2.getType() instanceof BvType, "Bitvector instructions only supports bitvector types!");
        checkState(instruction.getRetVar().isPresent(), "Instruction must have return variable");
        foldExpression(instruction, functionState, blockState, null, BvExprs.LogicShiftRight(cast(op1.getExpr(functionState.getValues()), (BvType) op2.getType()), cast(op2.getExpr(functionState.getValues()), (BvType) op2.getType())), 0);

    }

    private void ashr(Instruction instruction, GlobalState globalState, FunctionState functionState, BlockState blockState) {
        Argument op1 = instruction.getArguments().get(0);
        Argument op2 = instruction.getArguments().get(1);

        checkState(op1.getType() instanceof BvType, "Bitvector instructions only supports bitvector types!");
        checkState(op2.getType() instanceof BvType, "Bitvector instructions only supports bitvector types!");
        checkState(instruction.getRetVar().isPresent(), "Instruction must have return variable");
        foldExpression(instruction, functionState, blockState, null, BvExprs.ArithShiftRight(cast(op1.getExpr(functionState.getValues()), (BvType) op2.getType()), cast(op2.getExpr(functionState.getValues()), (BvType) op2.getType())), 0);

    }

    private void and(Instruction instruction, GlobalState globalState, FunctionState functionState, BlockState blockState) {
        Argument op1 = instruction.getArguments().get(0);
        Argument op2 = instruction.getArguments().get(1);
        checkState(instruction.getRetVar().isPresent(), "Instruction must have return variable");

        if (op1.getType() instanceof BoolType && op2.getType() instanceof BoolType) {
            foldExpression(instruction, functionState, blockState, null, BoolExprs.And(List.of(cast(op1.getExpr(functionState.getValues()), (BoolType) op2.getType()), cast(op2.getExpr(functionState.getValues()), (BoolType) op2.getType()))), 0);
            return;
        }

        checkState(op1.getType() instanceof BvType, "Bitvector instructions only supports bitvector types!");
        checkState(op2.getType() instanceof BvType, "Bitvector instructions only supports bitvector types!");
        foldExpression(instruction, functionState, blockState, null, BvExprs.And(List.of(cast(op1.getExpr(functionState.getValues()), (BvType) op2.getType()), cast(op2.getExpr(functionState.getValues()), (BvType) op2.getType()))), 0);
    }

    private void or(Instruction instruction, GlobalState globalState, FunctionState functionState, BlockState blockState) {
        Argument op1 = instruction.getArguments().get(0);
        Argument op2 = instruction.getArguments().get(1);

        checkState(instruction.getRetVar().isPresent(), "Instruction must have return variable");

        if (op1.getType() instanceof BoolType && op2.getType() instanceof BoolType) {
            foldExpression(instruction, functionState, blockState, null, BoolExprs.Or(List.of(cast(op1.getExpr(functionState.getValues()), (BoolType) op2.getType()), cast(op2.getExpr(functionState.getValues()), (BoolType) op2.getType()))), 0);
            return;
        }
        checkState(op1.getType() instanceof BvType, "Bitvector instructions only supports bitvector types!");
        checkState(op2.getType() instanceof BvType, "Bitvector instructions only supports bitvector types!");
        checkState(instruction.getRetVar().isPresent(), "Instruction must have return variable");
        foldExpression(instruction, functionState, blockState, null, BvExprs.Or(List.of(cast(op1.getExpr(functionState.getValues()), (BvType) op2.getType()), cast(op2.getExpr(functionState.getValues()), (BvType) op2.getType()))), 0);
    }

    private void xor(Instruction instruction, GlobalState globalState, FunctionState functionState, BlockState blockState) {
        Argument op1 = instruction.getArguments().get(0);
        Argument op2 = instruction.getArguments().get(1);
        checkState(instruction.getRetVar().isPresent(), "Instruction must have return variable");

        if (op1.getType() instanceof BoolType && op2.getType() instanceof BoolType) {
            foldExpression(instruction, functionState, blockState, null, BoolExprs.Xor(cast(op1.getExpr(functionState.getValues()), (BoolType) op2.getType()), cast(op2.getExpr(functionState.getValues()), (BoolType) op2.getType())), 0);
            return;
        }
        checkState(op1.getType() instanceof BvType, "Bitvector instructions only supports bitvector types!");
        checkState(op2.getType() instanceof BvType, "Bitvector instructions only supports bitvector types!");
        foldExpression(instruction, functionState, blockState, null, BvExprs.Xor(List.of(cast(op1.getExpr(functionState.getValues()), (BvType) op2.getType()), cast(op2.getExpr(functionState.getValues()), (BvType) op2.getType()))), 0);

    }
}
