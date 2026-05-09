package hu.bme.mit.theta.analysis.algorithm.lazy.expr;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.TransFunc;
import hu.bme.mit.theta.analysis.expr.BasicExprState;
import hu.bme.mit.theta.analysis.unit.UnitPrec;

import java.util.Collection;
import java.util.Collections;

public class LazyExprTransFunc<A extends Action> implements TransFunc<BasicExprState, A, UnitPrec> {

    private final ExprPost<A> exprPost;

    private LazyExprTransFunc(final ExprPost<A> exprPost) {
        this.exprPost = exprPost;
    }

    public static <A extends Action> LazyExprTransFunc<A> create(final ExprPost<A> exprPost) {
        return new LazyExprTransFunc<>(exprPost);
    }

    @Override
    public Collection<? extends BasicExprState> getSuccStates(final BasicExprState state, final A action, final UnitPrec prec) {
        return Collections.singleton(exprPost.post(state, action));
    }
}