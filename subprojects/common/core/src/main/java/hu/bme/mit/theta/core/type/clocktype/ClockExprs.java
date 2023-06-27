package hu.bme.mit.theta.core.type.clocktype;

import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.inttype.IntType;

public final class ClockExprs {

    private ClockExprs() {
    }

    public static ClockType Clock() {
        return ClockType.getInstance();
    }

    public static ClockLtExpr Lt(final Expr<ClockType> clock, final Expr<IntType> value) {
        return ClockLtExpr.of(clock, value);
    }

    public static ClockLeqExpr Leq(final Expr<ClockType> clock, final Expr<IntType> value) {
        return ClockLeqExpr.of(clock, value);
    }

    public static ClockGtExpr Gt(final Expr<ClockType> clock, final Expr<IntType> value) {
        return ClockGtExpr.of(clock, value);
    }

    public static ClockGeqExpr Geq(final Expr<ClockType> clock, final Expr<IntType> value) {
        return ClockGeqExpr.of(clock, value);
    }

    public static ClockEqExpr Eq(final Expr<ClockType> clock, final Expr<IntType> value) {
        return ClockEqExpr.of(clock, value);
    }

    public static ClockDiffExpr Diff(final Expr<ClockType> leftClock, final Expr<ClockType> rightClock) {
        return ClockDiffExpr.of(leftClock, rightClock);
    }
}
