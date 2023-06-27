package hu.bme.mit.theta.core.type.clocktype;

import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.inttype.IntType;

public final class ClockLtExpr extends ClockConstraintExpr {

    private static final ClockConstraintRel REL = ClockConstraintRel.LT;
    private static final String OPERATOR_LABEL = "<";

    protected ClockLtExpr(Expr<ClockType> clock, Expr<IntType> value) {
        super(clock, value);
    }

    public static ClockLtExpr of(final Expr<ClockType> clock, final Expr<IntType> value) {
        return new ClockLtExpr(clock, value);
    }

    @Override
    public ClockLtExpr with(Expr<ClockType> clock, Expr<IntType> value) {
        if (clock == getLeftOp() && value == getRightOp()) {
            return this;
        } else {
            return ClockLtExpr.of(clock, value);
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
