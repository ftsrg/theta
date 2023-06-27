package hu.bme.mit.theta.core.type.clocktype;

import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.inttype.IntType;

public final class ClockGtExpr extends ClockConstraintExpr {

    private static final ClockConstraintRel REL = ClockConstraintRel.GT;
    private static final String OPERATOR_LABEL = ">";

    protected ClockGtExpr(Expr<ClockType> clock, Expr<IntType> value) {
        super(clock, value);
    }

    public static ClockGtExpr of(final Expr<ClockType> clock, final Expr<IntType> value) {
        return new ClockGtExpr(clock, value);
    }

    @Override
    public ClockGtExpr with(Expr<ClockType> clock, Expr<IntType> value) {
        if (clock == getLeftOp() && value == getRightOp()) {
            return this;
        } else {
            return ClockGtExpr.of(clock, value);
        }
    }

    @Override
    public ClockConstraintRel getRel() {
        return REL;
    }

    @Override
    public String getOperatorLabel() {
        return OPERATOR_LABEL;
    }
}
