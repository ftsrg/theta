package hu.bme.mit.theta.analysis.algorithm.lazy.expr;

import com.google.common.collect.ImmutableList;
import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.InvTransFunc;
import hu.bme.mit.theta.analysis.expr.BasicExprState;
import hu.bme.mit.theta.analysis.unit.UnitPrec;

import java.util.Collection;

public class ExprInvTransFunc<A extends Action> implements InvTransFunc<BasicExprState, A, UnitPrec> {

    private final ExprActionPre<A> exprActionPre;

    private ExprInvTransFunc(final ExprActionPre<A> exprActionPre) {
        this.exprActionPre = exprActionPre;
    }

    public static <A extends Action> ExprInvTransFunc<A> create(final ExprActionPre<A> exprActionPre) {
        return new ExprInvTransFunc<>(exprActionPre);
    }

    @Override
    public Collection<? extends BasicExprState> getPreStates(BasicExprState state, A action, UnitPrec prec) {
        return ImmutableList.of(BasicExprState.of(exprActionPre.pre(state.toExpr(), action)));
    }
}
