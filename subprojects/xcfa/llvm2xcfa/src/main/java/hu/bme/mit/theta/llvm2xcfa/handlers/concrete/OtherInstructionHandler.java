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
import hu.bme.mit.theta.common.Tuple4;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.stmt.Stmt;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolExprs;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.type.inttype.IntType;
import hu.bme.mit.theta.core.type.rattype.RatExprs;
import hu.bme.mit.theta.core.type.rattype.RatType;
import hu.bme.mit.theta.llvm2xcfa.LlvmMetadata;
import hu.bme.mit.theta.llvm2xcfa.handlers.BaseInstructionHandler;
import hu.bme.mit.theta.llvm2xcfa.handlers.Instruction;
import hu.bme.mit.theta.llvm2xcfa.handlers.arguments.Argument;
import hu.bme.mit.theta.llvm2xcfa.handlers.arguments.RegArgument;
import hu.bme.mit.theta.llvm2xcfa.handlers.arguments.StringArgument;
import hu.bme.mit.theta.llvm2xcfa.handlers.states.BlockState;
import hu.bme.mit.theta.llvm2xcfa.handlers.states.FunctionState;
import hu.bme.mit.theta.llvm2xcfa.handlers.states.GlobalState;
import hu.bme.mit.theta.llvm2xcfa.handlers.utils.PlaceholderAssignmentStmt;
import hu.bme.mit.theta.xcfa.model.EmptyMetaData;
import hu.bme.mit.theta.xcfa.model.SequenceLabel;
import hu.bme.mit.theta.xcfa.model.StmtLabel;
import hu.bme.mit.theta.xcfa.model.XcfaEdge;
import hu.bme.mit.theta.xcfa.model.XcfaLocation;

import java.util.ArrayList;
import java.util.List;
import java.util.Optional;

import static com.google.common.base.Preconditions.checkState;
import static hu.bme.mit.theta.core.stmt.Stmts.Assign;
import static hu.bme.mit.theta.core.stmt.Stmts.Havoc;
import static hu.bme.mit.theta.core.type.anytype.Exprs.Ite;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Eq;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Geq;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Gt;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Leq;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Lt;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Neq;
import static hu.bme.mit.theta.core.utils.TypeUtils.cast;
import static hu.bme.mit.theta.llvm2xcfa.Utils.foldExpression;
import static hu.bme.mit.theta.llvm2xcfa.Utils.getOrCreateVar;

public class OtherInstructionHandler extends BaseInstructionHandler {
    @Override
    public void handleInstruction(Instruction instruction, GlobalState globalState, FunctionState functionState, BlockState blockState) {
        switch (instruction.getOpName()) {
            case "icmp":
                icmp(instruction, globalState, functionState, blockState);
                break;
            case "fcmp":
                fcmp(instruction, globalState, functionState, blockState);
                break;
            case "phi":
                phi(instruction, globalState, functionState, blockState);
                break;
            case "select":
                select(instruction, globalState, functionState, blockState);
                break;
            case "call":
                call(instruction, globalState, functionState, blockState);
                break;
            case "freeze":
            case "va_arg":
            case "landingpad":
            case "catchpad":
            case "cleanuppad":
                break;
            default:
                super.handleInstruction(instruction, globalState, functionState, blockState);
                break;
        }

    }

    private void call(Instruction instruction, GlobalState globalState, FunctionState functionState, BlockState blockState) {
        Argument functionName = instruction.getArguments().get(instruction.getArguments().size() - 1);
        XcfaLocation newLoc = new XcfaLocation(blockState.getName() + "_" + blockState.getBlockCnt());
        if (globalState.getProcedures().stream().anyMatch(objects -> objects.get1().equals(functionName.getName()))) {
            System.err.println("More than one function.");
            System.exit(-80);
        } else {
            List<Stmt> stmts = new ArrayList<>();
            if (instruction.getRetVar().isPresent()) {
                stmts.add(havocVar(instruction.getRetVar().get(), functionState, blockState));
            }
            for (Argument argument : instruction.getArguments()) {
                Tuple2<VarDecl<?>, Integer> objects = functionState.getLocalVars().get(argument.getName());
                if (objects != null && objects.get2() > 0)
                    stmts.add(havocVar(argument, functionState, blockState));
            }
            XcfaEdge edge = new XcfaEdge(blockState.getLastLocation(), newLoc, new SequenceLabel(stmts.stream().map(stmt -> new StmtLabel(stmt, EmptyMetaData.INSTANCE)).toList()), new LlvmMetadata(instruction.getLineNumber()));
            functionState.getProcedureBuilder().addLoc(newLoc);
            functionState.getProcedureBuilder().addEdge(edge);
        }
        blockState.setLastLocation(newLoc);
    }


    private Stmt havocVar(Argument reg, FunctionState functionState, BlockState blockState) {
        VarDecl<?> callVar = getOrCreateVar(functionState, reg);
        return Havoc(callVar);
    }

    private void select(Instruction instruction, GlobalState globalState, FunctionState functionState, BlockState blockState) {
        Argument cond = instruction.getArguments().get(0);
        Argument op1 = instruction.getArguments().get(1);
        Argument op2 = instruction.getArguments().get(2);

        checkState(cond.getType() == BoolType.getInstance(), "Select only supports boolean condition!");
        checkState(op1.getType().equals(op2.getType()), "Select only supports common types!");
        checkState(instruction.getRetVar().isPresent(), "Instruction must have return variable");
        Expr<?> expr1 = op1.getExpr(functionState.getValues());
        //TODO: what to do, when null?
        Expr<?> expr2 = op2.getExpr(functionState.getValues());
        foldExpression(instruction, functionState, blockState, null, Ite(cast(cond.getExpr(functionState.getValues()), BoolType.getInstance()), cast(expr1, expr1.getType()), cast(expr2, expr1.getType())), 0);
    }

    // Phi nodes are the only possible place where an argument might not be known yet.
    private void phi(Instruction instruction, GlobalState globalState, FunctionState functionState, BlockState blockState) {
        Optional<RegArgument> retVar = instruction.getRetVar();
        checkState(retVar.isPresent(), "Return var must be present!");
        VarDecl<?> phiVar = getOrCreateVar(functionState, retVar.get());
        for (int i = 0; i < (instruction.getArguments().size()) / 2; ++i) {
            Argument block = instruction.getArguments().get(2 * i + 1);
            Argument value = instruction.getArguments().get(2 * i);
            Tuple2<String, String> key = Tuple2.of(block.getName(), blockState.getName());
            Tuple4<XcfaLocation, XcfaLocation, List<Stmt>, Integer> val = functionState.getInterBlockEdges().getOrDefault(key, Tuple4.of(new XcfaLocation(key.get1()), new XcfaLocation(key.get2()), new ArrayList<>(), instruction.getLineNumber()));
            checkState(phiVar.getType().equals(value.getType()), "phiVar and value has to be of the same type!");
            Stmt stmt;
            Expr<?> expr;
            if ((expr = value.getExpr(functionState.getValues())) != null) {
                if (!phiVar.getRef().equals(expr)) {
                    stmt = Assign(cast(phiVar, phiVar.getType()), cast(expr, phiVar.getType()));
                    val.get3().add(stmt);
                }
            } else {
                stmt = PlaceholderAssignmentStmt.of(phiVar, value);
                val.get3().add(stmt);
            }
            functionState.getInterBlockEdges().put(key, val);
        }
    }

    private void fcmp(Instruction instruction, GlobalState globalState, FunctionState functionState, BlockState blockState) {
        Argument op1 = instruction.getArguments().get(0);
        Argument op2 = instruction.getArguments().get(1);
        Argument op3 = instruction.getArguments().get(2);

        checkState(op1 instanceof StringArgument, "Icmp has to have string argument as first operand!");
        checkState(op2.getType() == RatType.getInstance(), "Icmp only supports integer types!");
        checkState(op3.getType() == RatType.getInstance(), "Icmp only supports integer types!");
        checkState(instruction.getRetVar().isPresent(), "Instruction must have return variable");
        switch (op1.getName()) {
            case "ueq":
            case "oeq":
                foldExpression(instruction, functionState, blockState, null, RatExprs.Eq(cast(op2.getExpr(functionState.getValues()), RatType.getInstance()), cast(op3.getExpr(functionState.getValues()), RatType.getInstance())), 0);
                break;
            case "one":
            case "une":
                foldExpression(instruction, functionState, blockState, null, RatExprs.Neq(cast(op2.getExpr(functionState.getValues()), RatType.getInstance()), cast(op3.getExpr(functionState.getValues()), RatType.getInstance())), 0);
                break;
            case "ugt":
            case "ogt":
                foldExpression(instruction, functionState, blockState, null, RatExprs.Gt(cast(op2.getExpr(functionState.getValues()), RatType.getInstance()), cast(op3.getExpr(functionState.getValues()), RatType.getInstance())), 0);
                break;
            case "uge":
            case "oge":
                foldExpression(instruction, functionState, blockState, null, RatExprs.Geq(cast(op2.getExpr(functionState.getValues()), RatType.getInstance()), cast(op3.getExpr(functionState.getValues()), RatType.getInstance())), 0);
                break;
            case "ult":
            case "olt":
                foldExpression(instruction, functionState, blockState, null, RatExprs.Lt(cast(op2.getExpr(functionState.getValues()), RatType.getInstance()), cast(op3.getExpr(functionState.getValues()), RatType.getInstance())), 0);
                break;
            case "ole":
            case "ule":
                foldExpression(instruction, functionState, blockState, null, RatExprs.Leq(cast(op2.getExpr(functionState.getValues()), RatType.getInstance()), cast(op3.getExpr(functionState.getValues()), RatType.getInstance())), 0);
                break;
            case "ord":
            case "true":
                foldExpression(instruction, functionState, blockState, null, BoolExprs.True(), 0);
                break;
            case "false":
                foldExpression(instruction, functionState, blockState, null, BoolExprs.False(), 0);
                break;
            default:
                throw new IllegalStateException("Unexpected value: " + op1.getName());
        }
    }

    private void icmp(Instruction instruction, GlobalState globalState, FunctionState functionState, BlockState blockState) {
        Argument op1 = instruction.getArguments().get(0);
        Argument op2 = instruction.getArguments().get(1);
        Argument op3 = instruction.getArguments().get(2);

        checkState(op1 instanceof StringArgument, "Icmp has to have string argument as first operand!");
        checkState(op2.getType() == IntType.getInstance(), "Icmp only supports integer types!");
        checkState(op3.getType() == IntType.getInstance(), "Icmp only supports integer types!");
        checkState(instruction.getRetVar().isPresent(), "Instruction must have return variable");
        switch (op1.getName()) {
            case "eq":
                foldExpression(instruction, functionState, blockState, null, Eq(cast(op2.getExpr(functionState.getValues()), IntType.getInstance()), cast(op3.getExpr(functionState.getValues()), IntType.getInstance())), 0);
                break;
            case "ne":
                foldExpression(instruction, functionState, blockState, null, Neq(cast(op2.getExpr(functionState.getValues()), IntType.getInstance()), cast(op3.getExpr(functionState.getValues()), IntType.getInstance())), 0);
                break;
            case "ugt":
            case "sgt":
                foldExpression(instruction, functionState, blockState, null, Gt(cast(op2.getExpr(functionState.getValues()), IntType.getInstance()), cast(op3.getExpr(functionState.getValues()), IntType.getInstance())), 0);
                break;
            case "uge":
            case "sge":
                foldExpression(instruction, functionState, blockState, null, Geq(cast(op2.getExpr(functionState.getValues()), IntType.getInstance()), cast(op3.getExpr(functionState.getValues()), IntType.getInstance())), 0);
                break;
            case "ult":
            case "slt":
                foldExpression(instruction, functionState, blockState, null, Lt(cast(op2.getExpr(functionState.getValues()), IntType.getInstance()), cast(op3.getExpr(functionState.getValues()), IntType.getInstance())), 0);
                break;
            case "ule":
            case "sle":
                foldExpression(instruction, functionState, blockState, null, Leq(cast(op2.getExpr(functionState.getValues()), IntType.getInstance()), cast(op3.getExpr(functionState.getValues()), IntType.getInstance())), 0);
                break;
            default:
                throw new IllegalStateException("Unexpected value: " + op1.getName());
        }
    }
}
