package hu.bme.mit.theta.analysis.expr;

import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.utils.ExprUtils;

public final class SyntacticExprMeetStrategy implements ExprLattice.MeetStrategy {

    private final BasicExprMeetStrategy basicMeetStrategy;

    private static final SyntacticExprMeetStrategy INSTANCE = new SyntacticExprMeetStrategy();

    private SyntacticExprMeetStrategy() {
        basicMeetStrategy = BasicExprMeetStrategy.getInstance();
    }

    public static SyntacticExprMeetStrategy getInstance() {
        return INSTANCE;
    }

    @Override
    public BasicExprState meet(final BasicExprState state1, final BasicExprState state2) {
        final Expr<BoolType> expr1 = state1.toExpr();
        final Expr<BoolType> expr2 = state2.toExpr();
        if (ExprUtils.getConjuncts(expr1).contains(expr2)) {
            return BasicExprState.of(expr1);
        }
        if (ExprUtils.getConjuncts(expr2).contains(expr1)) {
            return BasicExprState.of(expr2);
        }
        return basicMeetStrategy.meet(state1, state2);
    }
}
