/*
 *  Copyright 2026 Budapest University of Technology and Economics
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
package hu.bme.mit.theta.core.dsl.impl;

import hu.bme.mit.theta.common.DispatchTable;
import hu.bme.mit.theta.core.type.AndExpr;
import hu.bme.mit.theta.core.type.ArrayEqExpr;
import hu.bme.mit.theta.core.type.ArrayInitExpr;
import hu.bme.mit.theta.core.type.ArrayLitExpr;
import hu.bme.mit.theta.core.type.ArrayNeqExpr;
import hu.bme.mit.theta.core.type.ArrayReadExpr;
import hu.bme.mit.theta.core.type.ArrayWriteExpr;
import hu.bme.mit.theta.core.type.BinaryExpr;
import hu.bme.mit.theta.core.type.BvAddExpr;
import hu.bme.mit.theta.core.type.BvAndExpr;
import hu.bme.mit.theta.core.type.BvArithShiftRightExpr;
import hu.bme.mit.theta.core.type.BvConcatExpr;
import hu.bme.mit.theta.core.type.BvEqExpr;
import hu.bme.mit.theta.core.type.BvExtractExpr;
import hu.bme.mit.theta.core.type.BvLitExpr;
import hu.bme.mit.theta.core.type.BvLogicShiftRightExpr;
import hu.bme.mit.theta.core.type.BvMulExpr;
import hu.bme.mit.theta.core.type.BvNegExpr;
import hu.bme.mit.theta.core.type.BvNeqExpr;
import hu.bme.mit.theta.core.type.BvNotExpr;
import hu.bme.mit.theta.core.type.BvOrExpr;
import hu.bme.mit.theta.core.type.BvPosExpr;
import hu.bme.mit.theta.core.type.BvRotateLeftExpr;
import hu.bme.mit.theta.core.type.BvRotateRightExpr;
import hu.bme.mit.theta.core.type.BvSDivExpr;
import hu.bme.mit.theta.core.type.BvSExtExpr;
import hu.bme.mit.theta.core.type.BvSGeqExpr;
import hu.bme.mit.theta.core.type.BvSGtExpr;
import hu.bme.mit.theta.core.type.BvSLeqExpr;
import hu.bme.mit.theta.core.type.BvSLtExpr;
import hu.bme.mit.theta.core.type.BvSModExpr;
import hu.bme.mit.theta.core.type.BvSRemExpr;
import hu.bme.mit.theta.core.type.BvShiftLeftExpr;
import hu.bme.mit.theta.core.type.BvSignChangeExpr;
import hu.bme.mit.theta.core.type.BvSubExpr;
import hu.bme.mit.theta.core.type.BvToIntExpr;
import hu.bme.mit.theta.core.type.BvUDivExpr;
import hu.bme.mit.theta.core.type.BvUGeqExpr;
import hu.bme.mit.theta.core.type.BvUGtExpr;
import hu.bme.mit.theta.core.type.BvULeqExpr;
import hu.bme.mit.theta.core.type.BvULtExpr;
import hu.bme.mit.theta.core.type.BvURemExpr;
import hu.bme.mit.theta.core.type.BvXorExpr;
import hu.bme.mit.theta.core.type.BvZExtExpr;
import hu.bme.mit.theta.core.type.ExistsExpr;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.FalseExpr;
import hu.bme.mit.theta.core.type.ForallExpr;
import hu.bme.mit.theta.core.type.FpAbsExpr;
import hu.bme.mit.theta.core.type.FpAddExpr;
import hu.bme.mit.theta.core.type.FpDivExpr;
import hu.bme.mit.theta.core.type.FpEqExpr;
import hu.bme.mit.theta.core.type.FpFromBvExpr;
import hu.bme.mit.theta.core.type.FpGeqExpr;
import hu.bme.mit.theta.core.type.FpGtExpr;
import hu.bme.mit.theta.core.type.FpLeqExpr;
import hu.bme.mit.theta.core.type.FpLitExpr;
import hu.bme.mit.theta.core.type.FpLtExpr;
import hu.bme.mit.theta.core.type.FpMaxExpr;
import hu.bme.mit.theta.core.type.FpMinExpr;
import hu.bme.mit.theta.core.type.FpMulExpr;
import hu.bme.mit.theta.core.type.FpNegExpr;
import hu.bme.mit.theta.core.type.FpNeqExpr;
import hu.bme.mit.theta.core.type.FpPosExpr;
import hu.bme.mit.theta.core.type.FpRemExpr;
import hu.bme.mit.theta.core.type.FpSqrtExpr;
import hu.bme.mit.theta.core.type.FpSubExpr;
import hu.bme.mit.theta.core.type.FpToBvExpr;
import hu.bme.mit.theta.core.type.FpToFpExpr;
import hu.bme.mit.theta.core.type.IffExpr;
import hu.bme.mit.theta.core.type.ImplyExpr;
import hu.bme.mit.theta.core.type.IntAddExpr;
import hu.bme.mit.theta.core.type.IntDivExpr;
import hu.bme.mit.theta.core.type.IntEqExpr;
import hu.bme.mit.theta.core.type.IntGeqExpr;
import hu.bme.mit.theta.core.type.IntGtExpr;
import hu.bme.mit.theta.core.type.IntLeqExpr;
import hu.bme.mit.theta.core.type.IntLitExpr;
import hu.bme.mit.theta.core.type.IntLtExpr;
import hu.bme.mit.theta.core.type.IntModExpr;
import hu.bme.mit.theta.core.type.IntMulExpr;
import hu.bme.mit.theta.core.type.IntNegExpr;
import hu.bme.mit.theta.core.type.IntNeqExpr;
import hu.bme.mit.theta.core.type.IntPosExpr;
import hu.bme.mit.theta.core.type.IntRemExpr;
import hu.bme.mit.theta.core.type.IntSubExpr;
import hu.bme.mit.theta.core.type.IntToRatExpr;
import hu.bme.mit.theta.core.type.IteExpr;
import hu.bme.mit.theta.core.type.MultiaryExpr;
import hu.bme.mit.theta.core.type.NotExpr;
import hu.bme.mit.theta.core.type.OrExpr;
import hu.bme.mit.theta.core.type.PrimeExpr;
import hu.bme.mit.theta.core.type.RatAddExpr;
import hu.bme.mit.theta.core.type.RatDivExpr;
import hu.bme.mit.theta.core.type.RatEqExpr;
import hu.bme.mit.theta.core.type.RatGeqExpr;
import hu.bme.mit.theta.core.type.RatGtExpr;
import hu.bme.mit.theta.core.type.RatLeqExpr;
import hu.bme.mit.theta.core.type.RatLitExpr;
import hu.bme.mit.theta.core.type.RatLtExpr;
import hu.bme.mit.theta.core.type.RatMulExpr;
import hu.bme.mit.theta.core.type.RatNegExpr;
import hu.bme.mit.theta.core.type.RatNeqExpr;
import hu.bme.mit.theta.core.type.RatPosExpr;
import hu.bme.mit.theta.core.type.RatSubExpr;
import hu.bme.mit.theta.core.type.RefExpr;
import hu.bme.mit.theta.core.type.TrueExpr;
import hu.bme.mit.theta.core.type.UnaryExpr;
import hu.bme.mit.theta.core.type.XorExpr;
import hu.bme.mit.theta.core.type.bvtype.*;
import java.util.Arrays;
import java.util.stream.Collectors;

public final class ExprWriter {

    private final DispatchTable<String> table;

    private static class LazyHolder {

        private static final ExprWriter INSTANCE = new ExprWriter();
    }

    public static ExprWriter instance() {
        return LazyHolder.INSTANCE;
    }

    private ExprWriter() {
        table =
                DispatchTable.<String>builder()

                        // Boolean

                        .addCase(NotExpr.class, e -> prefixUnary(e, "not "))
                        .addCase(ImplyExpr.class, e -> infixBinary(e, " imply "))
                        .addCase(IffExpr.class, e -> infixBinary(e, " iff "))
                        .addCase(AndExpr.class, e -> infixMultiary(e, " and "))
                        .addCase(OrExpr.class, e -> infixMultiary(e, " or "))
                        .addCase(XorExpr.class, e -> infixBinary(e, " xor "))
                        .addCase(TrueExpr.class, e -> "true")
                        .addCase(FalseExpr.class, e -> "false")
                        .addCase(ForallExpr.class, this::forall)
                        .addCase(ExistsExpr.class, this::exists)

                        // Integer

                        .addCase(IntAddExpr.class, e -> infixMultiary(e, " + "))
                        .addCase(IntSubExpr.class, e -> infixBinary(e, " - "))
                        .addCase(IntPosExpr.class, e -> prefixUnary(e, "+"))
                        .addCase(IntNegExpr.class, e -> prefixUnary(e, "-"))
                        .addCase(IntMulExpr.class, e -> infixMultiary(e, " * "))
                        .addCase(IntDivExpr.class, e -> infixBinary(e, " / "))
                        .addCase(IntModExpr.class, e -> infixBinary(e, " mod "))
                        .addCase(IntRemExpr.class, e -> infixBinary(e, " rem "))
                        .addCase(IntEqExpr.class, e -> infixBinary(e, " = "))
                        .addCase(IntNeqExpr.class, e -> infixBinary(e, " /= "))
                        .addCase(IntGeqExpr.class, e -> infixBinary(e, " >= "))
                        .addCase(IntGtExpr.class, e -> infixBinary(e, " > "))
                        .addCase(IntLeqExpr.class, e -> infixBinary(e, " <= "))
                        .addCase(IntLtExpr.class, e -> infixBinary(e, " < "))
                        .addCase(IntLitExpr.class, e -> e.getValue() + "")
                        .addCase(IntToRatExpr.class, e -> prefixUnary(e, "(rat)"))

                        // Rational

                        .addCase(RatAddExpr.class, e -> infixMultiary(e, " + "))
                        .addCase(RatSubExpr.class, e -> infixBinary(e, " - "))
                        .addCase(RatPosExpr.class, e -> prefixUnary(e, "+"))
                        .addCase(RatNegExpr.class, e -> prefixUnary(e, "-"))
                        .addCase(RatMulExpr.class, e -> infixMultiary(e, " * "))
                        .addCase(RatDivExpr.class, e -> infixBinary(e, " / "))
                        .addCase(RatEqExpr.class, e -> infixBinary(e, " = "))
                        .addCase(RatNeqExpr.class, e -> infixBinary(e, " /= "))
                        .addCase(RatGeqExpr.class, e -> infixBinary(e, " >= "))
                        .addCase(RatGtExpr.class, e -> infixBinary(e, " > "))
                        .addCase(RatLeqExpr.class, e -> infixBinary(e, " <= "))
                        .addCase(RatLtExpr.class, e -> infixBinary(e, " < "))
                        .addCase(RatLitExpr.class, e -> e.getNum() + "%" + e.getDenom())

                        // Bitvector

                        .addCase(BvConcatExpr.class, this::bvConcat)
                        .addCase(BvExtractExpr.class, this::bvExtract)
                        .addCase(BvZExtExpr.class, this::bvZExt)
                        .addCase(BvSExtExpr.class, this::bvSExt)
                        .addCase(BvAddExpr.class, e -> infixMultiary(e, " bvadd "))
                        .addCase(BvSubExpr.class, e -> infixBinary(e, " bvsub "))
                        .addCase(BvMulExpr.class, e -> infixMultiary(e, " bvmul "))
                        .addCase(BvUDivExpr.class, e -> infixBinary(e, " bvudiv "))
                        .addCase(BvSDivExpr.class, e -> infixBinary(e, " bvsdiv "))
                        .addCase(BvSModExpr.class, e -> infixBinary(e, " bvsmod "))
                        .addCase(BvURemExpr.class, e -> infixBinary(e, " bvurem "))
                        .addCase(BvSRemExpr.class, e -> infixBinary(e, " bvsrem "))
                        .addCase(BvPosExpr.class, e -> prefixUnary(e, "bvpos"))
                        .addCase(BvToIntExpr.class, e -> prefixUnary(e, "to_int"))
                        .addCase(BvSignChangeExpr.class, e -> prefixUnary(e, "bvsign"))
                        .addCase(BvNegExpr.class, e -> prefixUnary(e, "bvneg"))
                        .addCase(BvAndExpr.class, e -> infixMultiary(e, " bvand "))
                        .addCase(BvOrExpr.class, e -> infixMultiary(e, " bvor "))
                        .addCase(BvXorExpr.class, e -> infixMultiary(e, " bvxor "))
                        .addCase(BvNotExpr.class, e -> prefixUnary(e, "bvnot"))
                        .addCase(BvShiftLeftExpr.class, e -> infixBinary(e, " bvshl "))
                        .addCase(BvArithShiftRightExpr.class, e -> infixBinary(e, " bvashr "))
                        .addCase(BvLogicShiftRightExpr.class, e -> infixBinary(e, " bvlshr "))
                        .addCase(BvRotateLeftExpr.class, e -> infixBinary(e, " bvrol "))
                        .addCase(BvRotateRightExpr.class, e -> infixBinary(e, " bvror "))
                        .addCase(BvEqExpr.class, e -> infixBinary(e, " = "))
                        .addCase(BvNeqExpr.class, e -> infixBinary(e, " /= "))
                        .addCase(BvULtExpr.class, e -> infixBinary(e, " bvult "))
                        .addCase(BvULeqExpr.class, e -> infixBinary(e, " bvule "))
                        .addCase(BvUGtExpr.class, e -> infixBinary(e, " bvugt "))
                        .addCase(BvUGeqExpr.class, e -> infixBinary(e, " buge "))
                        .addCase(BvSLtExpr.class, e -> infixBinary(e, " bvslt "))
                        .addCase(BvSLeqExpr.class, e -> infixBinary(e, " bvsle "))
                        .addCase(BvSGtExpr.class, e -> infixBinary(e, " bvsgt "))
                        .addCase(BvSGeqExpr.class, e -> infixBinary(e, " bsge "))
                        .addCase(BvLitExpr.class, this::bvLit)

                        // Array

                        .addCase(ArrayReadExpr.class, this::arrayRead)
                        .addCase(ArrayWriteExpr.class, this::arrayWrite)
                        .addCase(ArrayEqExpr.class, e -> infixBinary(e, " = "))
                        .addCase(ArrayNeqExpr.class, e -> infixBinary(e, " /= "))
                        .addCase(ArrayLitExpr.class, this::arrayLit)
                        .addCase(ArrayInitExpr.class, this::arrayInit)

                        // FloatingPoint

                        .addCase(FpAbsExpr.class, e -> prefixUnary(e, " fpabs "))
                        .addCase(FpAddExpr.class, e -> infixMultiary(e, " + "))
                        .addCase(FpDivExpr.class, e -> infixBinary(e, " / "))
                        .addCase(FpEqExpr.class, e -> infixBinary(e, " == "))
                        .addCase(FpFromBvExpr.class, e -> prefixUnary(e, " fpfrombv "))
                        .addCase(FpGeqExpr.class, e -> infixBinary(e, " >= "))
                        .addCase(FpGtExpr.class, e -> infixBinary(e, " > "))
                        .addCase(FpLeqExpr.class, e -> infixBinary(e, " <= "))
                        .addCase(FpLtExpr.class, e -> infixBinary(e, " < "))
                        .addCase(FpLitExpr.class, FpLitExpr::toString)
                        .addCase(FpMaxExpr.class, e -> infixBinary(e, " fpmax "))
                        .addCase(FpMinExpr.class, e -> infixBinary(e, " fpmin "))
                        .addCase(FpMulExpr.class, e -> infixMultiary(e, " * "))
                        .addCase(FpNegExpr.class, e -> prefixUnary(e, " - "))
                        .addCase(FpNeqExpr.class, e -> infixBinary(e, " != "))
                        .addCase(FpPosExpr.class, e -> prefixUnary(e, " + "))
                        .addCase(FpRemExpr.class, e -> infixBinary(e, " % "))
                        .addCase(FpSqrtExpr.class, e -> prefixUnary(e, " sqrt "))
                        .addCase(FpSubExpr.class, e -> infixBinary(e, " - "))
                        .addCase(FpToBvExpr.class, e -> prefixUnary(e, " fptobv "))
                        .addCase(FpToFpExpr.class, e -> prefixUnary(e, " fptofp "))

                        // General

                        .addCase(RefExpr.class, e -> e.getDecl().getName())
                        .addCase(IteExpr.class, this::ite)
                        .addCase(PrimeExpr.class, e -> postfixUnary(e, "'"))
                        .addDefault(
                                e -> {
                                    throw new UnsupportedOperationException(
                                            "Expression not supported: " + e.toString());
                                })
                        .build();
    }

    public String write(final Expr<?> expr) {
        return table.dispatch(expr);
    }

    private String writeWithBrackets(final Expr<?> expr) {
        final boolean bracket = expr.getArity() > 0;
        return (bracket ? "(" : "") + write(expr) + (bracket ? ")" : "");
    }

    private String prefixUnary(final UnaryExpr<?, ?> expr, final String operator) {
        return operator + writeWithBrackets(expr.getOp());
    }

    private String postfixUnary(final UnaryExpr<?, ?> expr, final String operator) {
        return writeWithBrackets(expr.getOp()) + operator;
    }

    private String infixBinary(final BinaryExpr<?, ?> expr, final String operator) {
        return writeWithBrackets(expr.getLeftOp())
                + operator
                + writeWithBrackets(expr.getRightOp());
    }

    private String infixMultiary(final MultiaryExpr<?, ?> expr, final String operator) {
        final StringBuilder sb = new StringBuilder();
        final int ops = expr.getOps().size();
        for (int i = 0; i < ops; ++i) {
            sb.append(writeWithBrackets(expr.getOps().get(i)));
            if (i != ops - 1) {
                sb.append(operator);
            }
        }
        return sb.toString();
    }

    private String forall(final ForallExpr e) {
        // TODO Auto-generated method stub
        throw new UnsupportedOperationException("TODO: auto-generated method stub");
    }

    private String exists(final ExistsExpr e) {
        // TODO Auto-generated method stub
        throw new UnsupportedOperationException("TODO: auto-generated method stub");
    }

    private String bvConcat(final BvConcatExpr expr) {
        final StringBuilder sb = new StringBuilder();
        final int ops = expr.getOps().size();
        for (int i = 0; i < ops; ++i) {
            sb.append(writeWithBrackets(expr.getOps().get(i)));
            if (i != ops - 1) {
                sb.append(" ++ ");
            }
        }
        return sb.toString();
    }

    private String bvExtract(final BvExtractExpr e) {
        return writeWithBrackets(e.getBitvec())
                + "["
                + write(e.getFrom())
                + ":"
                + write(e.getUntil())
                + "]";
    }

    private String bvZExt(final BvZExtExpr e) {
        return "("
                + writeWithBrackets(e.getOp())
                + " zero_extend "
                + e.getExtendType().toString()
                + ")";
    }

    private String bvSExt(final BvSExtExpr e) {
        return "("
                + writeWithBrackets(e.getOp())
                + " sign_extend "
                + e.getExtendType().toString()
                + ")";
    }

    private String arrayRead(final ArrayReadExpr<?, ?> e) {
        return writeWithBrackets(e.getArray()) + "[" + write(e.getIndex()) + "]";
    }

    private String arrayWrite(final ArrayWriteExpr<?, ?> e) {
        return writeWithBrackets(e.getArray())
                + "["
                + write(e.getIndex())
                + " <- "
                + write(e.getElem())
                + "]";
    }

    private String ite(final IteExpr<?> expr) {
        final StringBuilder sb = new StringBuilder();
        sb.append("if ");
        sb.append(writeWithBrackets(expr.getCond()));
        sb.append(" then ");
        sb.append(writeWithBrackets(expr.getThen()));
        sb.append(" else ");
        sb.append(writeWithBrackets(expr.getElse()));
        return sb.toString();
    }

    private String bvLit(final BvLitExpr expr) {
        var value =
                Arrays.toString(expr.getValue())
                        .replace("true", "1")
                        .replace("false", "0")
                        .replace("[", "")
                        .replace("]", "")
                        .replace(",", "")
                        .replace(" ", "");
        return expr.getType().getSize() + "'b" + value;
    }

    private String arrayLit(final ArrayLitExpr<?, ?> expr) {
        return "["
                + expr.getElements().stream()
                        .map(e -> write(e.get1()) + " <- " + write(e.get2()))
                        .collect(Collectors.joining(", "))
                + "<"
                + expr.getType().getIndexType().toString()
                + ">default"
                + " <- "
                + write(expr.getElseElem())
                + "]";
    }

    private String arrayInit(final ArrayInitExpr<?, ?> expr) {
        return "["
                + expr.getElements().stream()
                        .map(e -> write(e.get1()) + " <- " + write(e.get2()))
                        .collect(Collectors.joining(", "))
                + "<"
                + expr.getType().getIndexType().toString()
                + ">default"
                + " <- "
                + write(expr.getElseElem())
                + "]";
    }
}
