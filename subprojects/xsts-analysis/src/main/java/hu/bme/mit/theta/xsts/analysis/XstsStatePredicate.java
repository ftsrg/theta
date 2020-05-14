package hu.bme.mit.theta.xsts.analysis;

import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.expr.ExprState;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.solver.Solver;

import java.util.function.Predicate;

public class XstsStatePredicate<P extends Predicate, S extends ExprState> implements Predicate<XstsState<S>>{

    private final P pred;

    public XstsStatePredicate(final P pred) {
        this.pred=pred;
    }

    @Override
    public boolean test(XstsState<S> state) {
        return state.isInitialized() && pred.test(state.getState());
    }
}
