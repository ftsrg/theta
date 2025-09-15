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
package hu.bme.mit.theta.core.dsl.impl;

import hu.bme.mit.theta.common.DispatchTable;
import hu.bme.mit.theta.core.type.BinaryExpr;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.MultiaryExpr;
import hu.bme.mit.theta.core.type.UnaryExpr;
import hu.bme.mit.theta.core.type.anytype.IteExpr;
import hu.bme.mit.theta.core.type.anytype.PrimeExpr;
import hu.bme.mit.theta.core.type.anytype.RefExpr;
import hu.bme.mit.theta.core.type.arraytype.ArrayEqExpr;
import hu.bme.mit.theta.core.type.arraytype.ArrayInitExpr;
import hu.bme.mit.theta.core.type.arraytype.ArrayLitExpr;
import hu.bme.mit.theta.core.type.arraytype.ArrayNeqExpr;
import hu.bme.mit.theta.core.type.arraytype.ArrayReadExpr;
import hu.bme.mit.theta.core.type.arraytype.ArrayWriteExpr;
import hu.bme.mit.theta.core.type.booltype.AndExpr;
import hu.bme.mit.theta.core.type.booltype.ExistsExpr;
import hu.bme.mit.theta.core.type.booltype.FalseExpr;
import hu.bme.mit.theta.core.type.booltype.ForallExpr;
import hu.bme.mit.theta.core.type.booltype.IffExpr;
import hu.bme.mit.theta.core.type.booltype.ImplyExpr;
import hu.bme.mit.theta.core.type.booltype.NotExpr;
import hu.bme.mit.theta.core.type.booltype.OrExpr;
import hu.bme.mit.theta.core.type.booltype.TrueExpr;
import hu.bme.mit.theta.core.type.booltype.XorExpr;
import hu.bme.mit.theta.core.type.bvtype.BvAddExpr;
import hu.bme.mit.theta.core.type.bvtype.BvAndExpr;
import hu.bme.mit.theta.core.type.bvtype.BvArithShiftRightExpr;
import hu.bme.mit.theta.core.type.bvtype.BvConcatExpr;
import hu.bme.mit.theta.core.type.bvtype.BvEqExpr;
import hu.bme.mit.theta.core.type.bvtype.BvExtractExpr;
import hu.bme.mit.theta.core.type.bvtype.BvLitExpr;
import hu.bme.mit.theta.core.type.bvtype.BvLogicShiftRightExpr;
import hu.bme.mit.theta.core.type.bvtype.BvMulExpr;
import hu.bme.mit.theta.core.type.bvtype.BvNegExpr;
import hu.bme.mit.theta.core.type.bvtype.BvNeqExpr;
import hu.bme.mit.theta.core.type.bvtype.BvNotExpr;
import hu.bme.mit.theta.core.type.bvtype.BvOrExpr;
import hu.bme.mit.theta.core.type.bvtype.BvPosExpr;
import hu.bme.mit.theta.core.type.bvtype.BvRotateLeftExpr;
import hu.bme.mit.theta.core.type.bvtype.BvRotateRightExpr;
import hu.bme.mit.theta.core.type.bvtype.BvSDivExpr;
import hu.bme.mit.theta.core.type.bvtype.BvSExtExpr;
import hu.bme.mit.theta.core.type.bvtype.BvSGeqExpr;
import hu.bme.mit.theta.core.type.bvtype.BvSGtExpr;
import hu.bme.mit.theta.core.type.bvtype.BvSLeqExpr;
import hu.bme.mit.theta.core.type.bvtype.BvSLtExpr;
import hu.bme.mit.theta.core.type.bvtype.BvSModExpr;
import hu.bme.mit.theta.core.type.bvtype.BvSRemExpr;
import hu.bme.mit.theta.core.type.bvtype.BvShiftLeftExpr;
import hu.bme.mit.theta.core.type.bvtype.BvSignChangeExpr;
import hu.bme.mit.theta.core.type.bvtype.BvSubExpr;
import hu.bme.mit.theta.core.type.bvtype.BvUDivExpr;
import hu.bme.mit.theta.core.type.bvtype.BvUGeqExpr;
import hu.bme.mit.theta.core.type.bvtype.BvUGtExpr;
import hu.bme.mit.theta.core.type.bvtype.BvULeqExpr;
import hu.bme.mit.theta.core.type.bvtype.BvULtExpr;
import hu.bme.mit.theta.core.type.bvtype.BvURemExpr;
import hu.bme.mit.theta.core.type.bvtype.BvXorExpr;
import hu.bme.mit.theta.core.type.bvtype.BvZExtExpr;
import hu.bme.mit.theta.core.type.fptype.FpAbsExpr;
import hu.bme.mit.theta.core.type.fptype.FpAddExpr;
import hu.bme.mit.theta.core.type.fptype.FpDivExpr;
import hu.bme.mit.theta.core.type.fptype.FpEqExpr;
import hu.bme.mit.theta.core.type.fptype.FpFromBvExpr;
import hu.bme.mit.theta.core.type.fptype.FpGeqExpr;
import hu.bme.mit.theta.core.type.fptype.FpGtExpr;
import hu.bme.mit.theta.core.type.fptype.FpLeqExpr;
import hu.bme.mit.theta.core.type.fptype.FpLitExpr;
import hu.bme.mit.theta.core.type.fptype.FpLtExpr;
import hu.bme.mit.theta.core.type.fptype.FpMaxExpr;
import hu.bme.mit.theta.core.type.fptype.FpMinExpr;
import hu.bme.mit.theta.core.type.fptype.FpMulExpr;
import hu.bme.mit.theta.core.type.fptype.FpNegExpr;
import hu.bme.mit.theta.core.type.fptype.FpNeqExpr;
import hu.bme.mit.theta.core.type.fptype.FpPosExpr;
import hu.bme.mit.theta.core.type.fptype.FpRemExpr;
import hu.bme.mit.theta.core.type.fptype.FpSqrtExpr;
import hu.bme.mit.theta.core.type.fptype.FpSubExpr;
import hu.bme.mit.theta.core.type.fptype.FpToBvExpr;
import hu.bme.mit.theta.core.type.fptype.FpToFpExpr;
import hu.bme.mit.theta.core.type.inttype.IntAddExpr;
import hu.bme.mit.theta.core.type.inttype.IntDivExpr;
import hu.bme.mit.theta.core.type.inttype.IntEqExpr;
import hu.bme.mit.theta.core.type.inttype.IntGeqExpr;
import hu.bme.mit.theta.core.type.inttype.IntGtExpr;
import hu.bme.mit.theta.core.type.inttype.IntLeqExpr;
import hu.bme.mit.theta.core.type.inttype.IntLitExpr;
import hu.bme.mit.theta.core.type.inttype.IntLtExpr;
import hu.bme.mit.theta.core.type.inttype.IntModExpr;
import hu.bme.mit.theta.core.type.inttype.IntMulExpr;
import hu.bme.mit.theta.core.type.inttype.IntNegExpr;
import hu.bme.mit.theta.core.type.inttype.IntNeqExpr;
import hu.bme.mit.theta.core.type.inttype.IntPosExpr;
import hu.bme.mit.theta.core.type.inttype.IntRemExpr;
import hu.bme.mit.theta.core.type.inttype.IntSubExpr;
import hu.bme.mit.theta.core.type.inttype.IntToRatExpr;
import hu.bme.mit.theta.core.type.rattype.RatAddExpr;
import hu.bme.mit.theta.core.type.rattype.RatDivExpr;
import hu.bme.mit.theta.core.type.rattype.RatEqExpr;
import hu.bme.mit.theta.core.type.rattype.RatGeqExpr;
import hu.bme.mit.theta.core.type.rattype.RatGtExpr;
import hu.bme.mit.theta.core.type.rattype.RatLeqExpr;
import hu.bme.mit.theta.core.type.rattype.RatLitExpr;
import hu.bme.mit.theta.core.type.rattype.RatLtExpr;
import hu.bme.mit.theta.core.type.rattype.RatMulExpr;
import hu.bme.mit.theta.core.type.rattype.RatNegExpr;
import hu.bme.mit.theta.core.type.rattype.RatNeqExpr;
import hu.bme.mit.theta.core.type.rattype.RatPosExpr;
import hu.bme.mit.theta.core.type.rattype.RatSubExpr;
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
