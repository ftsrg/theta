package hu.bme.mit.theta.core.type.clocktype;

import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.inttype.IntType;

public final class ClockLeqExpr extends ClockConstraintExpr {

    private static final ClockConstraintRel REL = ClockConstraintRel.LEQ;
    private static final String OPERATOR_LABEL = "<=";

    protected ClockLeqExpr(Expr<ClockType> clock, Expr<IntType> value) {
        super(clock, value);
    }

    public static ClockLeqExpr of(final Expr<ClockType> clock, final Expr<IntType> value) {
        return new ClockLeqExpr(clock, value);
    }

    @Override
    public ClockLeqExpr with(Expr<ClockType> clock, Expr<IntType> value) {
        if (clock == getLeftOp() && value == getRightOp()) {
            return this;
        } else {
            return ClockLeqExpr.of(clock, value);
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
