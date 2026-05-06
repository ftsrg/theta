package hu.bme.mit.theta.analysis.algorithm.lazy.expr;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.TransFunc;
import hu.bme.mit.theta.analysis.expr.BasicExprState;
import hu.bme.mit.theta.analysis.unit.UnitPrec;

import java.util.Collection;
import java.util.Collections;

public class ExprTransFunc<A extends Action> implements TransFunc<BasicExprState, A, UnitPrec> {

    private final ExprActionPost<A> exprActionPost;

    private ExprTransFunc(final ExprActionPost<A> exprActionPost) {
        this.exprActionPost = exprActionPost;
    }

    public static <A extends Action> ExprTransFunc<A> create(final ExprActionPost<A> exprActionPost) {
        return new ExprTransFunc<>(exprActionPost);
    }

    @Override
    public Collection<? extends BasicExprState> getSuccStates(final BasicExprState state, final A action, final UnitPrec prec) {
        return Collections.singleton(exprActionPost.post(state, action));
    }
}