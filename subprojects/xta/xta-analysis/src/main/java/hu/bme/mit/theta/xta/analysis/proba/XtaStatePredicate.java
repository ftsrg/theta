package hu.bme.mit.theta.xta.analysis.proba;

import hu.bme.mit.theta.analysis.expr.ExprState;
import hu.bme.mit.theta.xta.analysis.XtaState;

import java.util.function.Predicate;

public class XtaStatePredicate <P extends Predicate, S extends ExprState> implements Predicate<XtaState<S>>{
    private final P pred;

    public XtaStatePredicate(final P pred) {
        this.pred = pred;
    }

    @Override
    public boolean test(XtaState<S> state) {
        return pred.test(state.getState());
    }
}
