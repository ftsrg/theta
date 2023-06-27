package hu.bme.mit.theta.core.type.clocktype;

import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.inttype.IntType;

public final class ClockGeqExpr extends ClockConstraintExpr {

    private static final ClockConstraintRel REL = ClockConstraintRel.GEQ;
    private static final String OPERATOR_LABEL = ">=";

    protected ClockGeqExpr(Expr<ClockType> clock, Expr<IntType> value) {
        super(clock, value);
    }

    public static ClockGeqExpr of(final Expr<ClockType> clock, final Expr<IntType> value) {
        return new ClockGeqExpr(clock, value);
    }

    @Override
    public ClockGeqExpr with(Expr<ClockType> clock, Expr<IntType> value) {
        if (clock == getLeftOp() && value == getRightOp()) {
            return this;
        } else {
            return ClockGeqExpr.of(clock, value);
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
