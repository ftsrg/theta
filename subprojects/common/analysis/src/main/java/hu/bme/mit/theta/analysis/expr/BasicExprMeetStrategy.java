package hu.bme.mit.theta.analysis.expr;

import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;

import static hu.bme.mit.theta.core.type.booltype.BoolExprs.And;

public final class BasicExprMeetStrategy implements ExprLattice.MeetStrategy {

    private static final BasicExprMeetStrategy INSTANCE = new BasicExprMeetStrategy();

    private BasicExprMeetStrategy() {
    }

    public static BasicExprMeetStrategy getInstance() {
        return INSTANCE;
    }

    @Override
    public BasicExprState meet(final BasicExprState state1, final BasicExprState state2) {
        final Expr<BoolType> andExpr = And(state1.toExpr(), state2.toExpr());
        return BasicExprState.of(andExpr);
    }
}
