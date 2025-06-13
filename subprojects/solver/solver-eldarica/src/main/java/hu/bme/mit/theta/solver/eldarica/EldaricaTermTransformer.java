/*
 *  Copyright 2025 Budapest University of Technology and Economics
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
package hu.bme.mit.theta.solver.eldarica;

import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.*;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.*;
import static hu.bme.mit.theta.core.type.booltype.SmartBoolExprs.And;
import static hu.bme.mit.theta.core.type.booltype.SmartBoolExprs.Or;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;
import static hu.bme.mit.theta.core.utils.TypeUtils.cast;
import static hu.bme.mit.theta.solver.eldarica.Utils.PredTermFormula.wrap;
import static hu.bme.mit.theta.solver.eldarica.Utils.getIterable;

import ap.parser.*;
import ap.terfor.preds.Predicate;
import hu.bme.mit.theta.core.decl.Decl;
import hu.bme.mit.theta.core.decl.ParamDecl;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.abstracttype.GeqExpr;
import hu.bme.mit.theta.core.type.arraytype.ArrayLitExpr;
import hu.bme.mit.theta.core.type.arraytype.ArrayReadExpr;
import hu.bme.mit.theta.core.type.arraytype.ArrayType;
import hu.bme.mit.theta.core.type.arraytype.ArrayWriteExpr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.type.bvtype.*;
import hu.bme.mit.theta.core.type.functype.FuncAppExpr;
import hu.bme.mit.theta.core.type.inttype.IntLitExpr;
import hu.bme.mit.theta.core.utils.BvUtils;
import java.math.BigInteger;
import java.util.Collections;
import java.util.LinkedList;
import java.util.List;
import org.jetbrains.annotations.NotNull;

public final class EldaricaTermTransformer {

    private final EldaricaSymbolTable symbolTable;

    public EldaricaTermTransformer(final EldaricaSymbolTable symbolTable) {
        this.symbolTable = symbolTable;
    }

    public Expr<?> toExpr(IExpression expr) {
        return toExpr(expr, List.of());
    }

    public Expr<?> toExpr(IExpression expr, List<ParamDecl<?>> params) {
        if (expr instanceof IFunApp funapp) {
            final List<Expr<?>> args = new LinkedList<>();
            for (ITerm iTerm : getIterable(funapp.args())) {
                args.add(toExpr(iTerm, params));
            }
            return handleFunction(funapp.fun().name(), args);
        } else if (expr instanceof IAtom atom) {
            final List<Expr<?>> args = new LinkedList<>();
            for (ITerm iTerm : getIterable(atom.args())) {
                args.add(toExpr(iTerm, params));
            }
            if (symbolTable.definesSymbol(wrap(atom.pred()))) {
                Expr<?> ret = symbolTable.getConst(wrap(atom.pred())).getRef();
                for (Expr<?> arg : args) {
                    ret = FuncAppExpr.create(ret, arg);
                }
                return ret;
            }
            return handleFunction(atom.pred().name(), args);
        } else if (expr instanceof IBinFormula binFormula) {
            final var lhs = (Expr<BoolType>) toExpr(binFormula.f1(), params);
            final var rhs = (Expr<BoolType>) toExpr(binFormula.f2(), params);
            return switch (binFormula.j().toString()) {
                case "Or" -> Or(List.of(lhs, rhs));
                case "And" -> And(List.of(lhs, rhs));
                default ->
                        throw new UnsupportedOperationException(
                                "Function (IBinFormula) %s not supported in backtransformation"
                                        .formatted(binFormula.j().toString()));
            };
        } else if (expr instanceof IIntFormula intFormula) {
            final var op = toExpr(intFormula.t(), params);
            final var zero =
                    op.getType().equals(Int())
                            ? IntLitExpr.of(BigInteger.ZERO)
                            : BvUtils.bigIntegerToNeutralBvLitExpr(
                                    BigInteger.ZERO, ((BvType) op.getType()).getSize());
            return switch (intFormula.rel().toString()) {
                case "GeqZero" -> GeqExpr.create2(op, zero);
                case "EqZero" -> Eq(op, zero);
                default ->
                        throw new UnsupportedOperationException(
                                "Function (IIntFormula) %s not supported in backtransformation"
                                        .formatted(intFormula.rel().toString()));
            };
        } else if (expr instanceof IEquation equation) {
            final var lhs = toExpr(equation.left(), params);
            final var rhs = toExpr(equation.right(), params);
            return Eq(lhs, rhs);
        } else if (expr instanceof INot not) {
            final var op = toExpr(not.subformula(), params);
            return Not(cast(op, Bool()));
        } else if (expr instanceof IPlus plus) {
            final var lhs = toExpr(plus.t1(), params);
            final var rhs = toExpr(plus.t2(), params);
            return Add(lhs, rhs);
        } else if (expr instanceof ITimes times) {
            final var lhs = toExpr(times.subterm(), params);
            final var rhs =
                    lhs.getType().equals(Int())
                            ? IntLitExpr.of(times.coeff().bigIntValue())
                            : BvUtils.bigIntegerToNeutralBvLitExpr(
                                    times.coeff().bigIntValue(),
                                    ((BvType) lhs.getType()).getSize());
            return Mul(List.of(lhs, rhs));
        } else if (expr instanceof ITermITE ite) {
            final var cond = toExpr(ite.cond(), params);
            final var left = toExpr(ite.left(), params);
            final var right = toExpr(ite.right(), params);
            return Ite((Expr<BoolType>) cond, left, right);
        } else if (expr instanceof ISortedVariable sortedVariable) {
            return params.get(sortedVariable.index()).getRef();
        } else if (expr instanceof IConstant constant) {
            if (symbolTable.definesSymbol(wrap(constant))) {
                return symbolTable.getConst(wrap(constant)).getRef();
            } else {
                throw new UnsupportedOperationException(
                        "Unknown constant %s in backtransformation".formatted(constant));
            }
        } else if (expr instanceof IIntLit) {
            return Int(((IIntLit) expr).value().bigIntValue());
        } else if (expr instanceof IBoolLit) {
            return Bool(((IBoolLit) expr).value());
        } else {
            throw new UnsupportedOperationException(
                    "Expression %s of type %s not supported in backtransformation"
                            .formatted(expr, expr.getClass().getSimpleName()));
        }
    }

    @NotNull private static Expr<?> handleFunction(String name, List<Expr<?>> args) {
        return switch (name) {
            case "FALSE" -> False();
            case "mod_cast" -> {
                if (args.get(0) instanceof IntLitExpr low
                        && args.get(1) instanceof IntLitExpr high) {
                    final var size = high.getValue().subtract(low.getValue()).bitLength();
                    if (args.get(2) instanceof IntLitExpr value) {
                        if (low.getValue().intValue() == 0
                                && BigInteger.ONE
                                        .shiftLeft(size)
                                        .subtract(BigInteger.ONE)
                                        .equals(high.getValue())) {
                            yield BvUtils.bigIntegerToUnsignedBvLitExpr(value.getValue(), size);
                        } else if (BigInteger.ONE
                                        .shiftLeft(size - 1)
                                        .negate()
                                        .equals(low.getValue())
                                && BigInteger.ONE
                                        .shiftLeft(size - 1)
                                        .subtract(BigInteger.ONE)
                                        .equals(high.getValue())) {
                            yield BvUtils.bigIntegerToSignedBvLitExpr(value.getValue(), size);
                        }
                    } else if (args.get(2).getType() instanceof BvType bvType) {
                        var value = (Expr<BvType>) args.get(2);
                        if (size == bvType.getSize()) {
                            if (low.getValue().intValue() == 0)
                                yield BvSignChangeExpr.create(value, BvType.of(size, false));
                            yield BvSignChangeExpr.create(value, BvType.of(size, true));
                        } else if (size > bvType.getSize()) {
                            if (bvType.getSigned()) {
                                yield BvSExtExpr.create(value, BvType.of(size));
                            } else {
                                yield BvZExtExpr.create(value, BvType.of(size));
                            }
                        } else {
                            yield BvExtractExpr.of(
                                    value,
                                    IntLitExpr.of(BigInteger.ZERO),
                                    IntLitExpr.of(BigInteger.valueOf(size - 1)));
                        }
                    }
                }
                throw new UnsupportedOperationException(
                        "Mod_cast only implemented for bitvectors! Got: %s, %s, %s"
                                .formatted(args.get(0), args.get(1), args.get(2)));
            }
            case "bv_add" -> BvAddExpr.create(List.of(args.get(1), args.get(2)));
            case "bv_and" -> BvAndExpr.create(List.of(args.get(1), args.get(2)));
            case "bv_ashr" -> BvArithShiftRightExpr.create(args.get(1), args.get(2));
            case "bv_lshr" -> BvLogicShiftRightExpr.create(args.get(1), args.get(2));
            case "bv_concat" -> BvConcatExpr.create(List.of(args.get(2), args.get(3)));
            case "bv_eq" -> BvEqExpr.create(args.get(1), args.get(2));
            case "bv_extract" -> BvExtractExpr.create(args.get(2), args.get(0), args.get(1));
            case "bv_mul" -> BvMulExpr.create(List.of(args.get(1), args.get(2)));
            case "bv_neg" -> BvNegExpr.create(args.get(1));
            case "bv_not" -> BvNotExpr.create(args.get(1));
            case "bv_or" -> BvOrExpr.create(List.of(args.get(1), args.get(2)));
            case "bv_pos" -> BvPosExpr.create(args.get(1));
            case "int_cast" -> BvToIntExpr.create(args.get(0));
            case "bv_sdiv" -> BvSDivExpr.create(args.get(1), args.get(2));
            case "bv_sge" -> BvSGeqExpr.create(args.get(1), args.get(2));
            case "bv_sgt" -> BvSGtExpr.create(args.get(1), args.get(2));
            case "bv_shl" -> BvShiftLeftExpr.create(args.get(1), args.get(2));
            case "bv_sle" -> BvSLeqExpr.create(args.get(1), args.get(2));
            case "bv_slt" -> BvSLtExpr.create(args.get(1), args.get(2));
            case "bv_smod" -> BvSModExpr.create(args.get(1), args.get(2));
            case "bv_srem" -> BvSRemExpr.create(args.get(1), args.get(2));
            case "bv_sub" -> BvSubExpr.create(args.get(1), args.get(2));
            case "bv_udiv" -> BvUDivExpr.create(args.get(1), args.get(2));
            case "bv_uge" -> BvUGeqExpr.create(args.get(1), args.get(2));
            case "bv_ugt" -> BvUGtExpr.create(args.get(1), args.get(2));
            case "bv_ule" -> BvULeqExpr.create(args.get(1), args.get(2));
            case "bv_ult" -> BvULtExpr.create(args.get(1), args.get(2));
            case "bv_urem" -> BvURemExpr.create(args.get(1), args.get(2));
            case "bv_xor" -> BvXorExpr.create(List.of(args.get(1), args.get(2)));
            case "zero_extend" ->
                    BvZExtExpr.create(
                            args.get(2),
                            BvType.of(
                                    ((BvType) args.get(2).getType()).getSize()
                                            + ((IntLitExpr) args.get(1)).getValue().intValue()));
            // arrays
            case "const" ->
                    ArrayLitExpr.of(
                            Collections.emptyList(),
                            (Expr<Type>) args.get(0),
                            ArrayType.of(
                                    Int(),
                                    args.get(0)
                                            .getType())); // TODO: what to do if index is not Int()?
            case "store" -> ArrayWriteExpr.create(args.get(0), args.get(1), args.get(2));
            case "select" -> ArrayReadExpr.create(args.get(0), args.get(1));
            default ->
                    throw new UnsupportedOperationException(
                            "Function %s(%s) not supported in backtransformation"
                                    .formatted(name, args));
        };
    }

    public Decl<?> toDecl(Predicate predicate) {
        final var wrapped = wrap(predicate);
        if (symbolTable.definesSymbol(wrapped)) {
            return symbolTable.getConst(wrapped);
        } else {
            throw new RuntimeException(
                    "Predicate %s not found in backtransformation".formatted(predicate));
        }
    }
}
