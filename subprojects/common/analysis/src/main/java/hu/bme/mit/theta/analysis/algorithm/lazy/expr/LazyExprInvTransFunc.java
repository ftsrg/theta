package hu.bme.mit.theta.analysis.algorithm.lazy.expr;

import com.google.common.collect.ImmutableList;
import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.InvTransFunc;
import hu.bme.mit.theta.analysis.expr.BasicExprState;
import hu.bme.mit.theta.analysis.unit.UnitPrec;

import java.util.Collection;

public class LazyExprInvTransFunc<A extends Action> implements InvTransFunc<BasicExprState, A, UnitPrec> {

    private final ExprPre<A> exprPre;

    private LazyExprInvTransFunc(final ExprPre<A> exprPre) {
        this.exprPre = exprPre;
    }

    public static <A extends Action> LazyExprInvTransFunc<A> create(final ExprPre<A> exprPre) {
        return new LazyExprInvTransFunc<>(exprPre);
    }

    @Override
    public Collection<? extends BasicExprState> getPreStates(BasicExprState state, A action, UnitPrec prec) {
        return ImmutableList.of(BasicExprState.of(exprPre.pre(state.toExpr(), action)));
    }
}
