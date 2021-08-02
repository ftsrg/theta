package hu.bme.mit.theta.core.type.fptype;

import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.bvtype.BvLitExpr;
import hu.bme.mit.theta.core.type.bvtype.BvType;

public final class FpExprs {
    private FpExprs() {}

    public static FpType FpType(final int exponent, final int significand) {
        return FpType.of(exponent, significand);
    }

    public static FpLitExpr Fp(boolean hidden, BvLitExpr exponent, BvLitExpr significand) {
        return FpLitExpr.of(hidden, exponent, significand);
    }

    public static FpAddExpr Add(final FpRoundingMode roundingMode, final Iterable<? extends Expr<FpType>> ops) {
        return FpAddExpr.of(roundingMode, ops);
    }

    public static FpSubExpr Sub(final FpRoundingMode roundingMode, final Expr<FpType> leftOp, final Expr<FpType> rightOp) {
        return FpSubExpr.of(roundingMode, leftOp, rightOp);
    }

    public static FpPosExpr Pos(final Expr<FpType> op) {
        return FpPosExpr.of(op);
    }

    public static FpNegExpr Neg(final Expr<FpType> op) {
        return FpNegExpr.of(op);
    }

    public static FpMulExpr Mul(final FpRoundingMode roundingMode, final Iterable<? extends Expr<FpType>> ops) {
        return FpMulExpr.of(roundingMode, ops);
    }

    public static FpDivExpr Div(final FpRoundingMode roundingMode, final Expr<FpType> leftOp, final Expr<FpType> rightOp) {
        return FpDivExpr.of(roundingMode, leftOp, rightOp);
    }

    public static FpRemExpr Rem(final FpRoundingMode roundingMode, final Expr<FpType> leftOp, final Expr<FpType> rightOp) {
        return FpRemExpr.of(roundingMode, leftOp, rightOp);
    }

    public static FpAbsExpr Abs(final Expr<FpType> op) {
        return FpAbsExpr.of(op);
    }

    public static FpFromBvExpr fromBv(final FpRoundingMode roundingMode, final Expr<BvType> sgn, final Expr<BvType> sig, final Expr<BvType> exp) {
        return FpFromBvExpr.of(roundingMode, sgn, sig, exp);
    }

    public static FpToBvExpr toBv(final FpRoundingMode roundingMode, final Expr<FpType> op, final int size, final boolean sgn) {
        return FpToBvExpr.of(roundingMode, op, size, sgn);
    }

    public static FpToFpExpr toFp(final FpRoundingMode roundingMode, final Expr<FpType> op, final int exp, final int sgn) {
        return FpToFpExpr.of(roundingMode, op, exp, sgn);
    }
}
