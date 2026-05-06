package hu.bme.mit.theta.analysis.algorithm.lazy;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.TransFunc;
import hu.bme.mit.theta.analysis.expr.ExprState;

import java.util.ArrayList;
import java.util.Collection;

import static com.google.common.base.Preconditions.checkNotNull;
import static java.util.stream.Collectors.toList;

public final class LazyTransFunc<SConcr extends State, SAbstr extends ExprState, A extends Action, P extends Prec> implements TransFunc<LazyState<SConcr, SAbstr>, A, P> {

    private final TransFunc<SConcr, A, P> concrTransFunc;
    private final InitAbstractor<SConcr, SAbstr> initAbstractor;

    private LazyTransFunc(final TransFunc<SConcr, A, P> concrTransFunc, final InitAbstractor<SConcr, SAbstr> initAbstractor){
        this.concrTransFunc = checkNotNull(concrTransFunc);
        this.initAbstractor = checkNotNull(initAbstractor);
    }

    public static <SConcr extends State, SAbstr extends ExprState, A extends Action, P extends Prec> LazyTransFunc<SConcr, SAbstr, A, P>
    create(final TransFunc<SConcr, A, P> concrTransFunc, final InitAbstractor<SConcr, SAbstr> initAbstractor) {
        return new LazyTransFunc<>(concrTransFunc, initAbstractor);
    }

    @Override
    public Collection<? extends LazyState<SConcr, SAbstr>> getSuccStates(LazyState<SConcr, SAbstr> state, A action, P prec) {
        final SConcr concrState = state.getConcrState();
        final Collection<SConcr> concrSuccStates = new ArrayList<>(concrTransFunc.getSuccStates(concrState, action, prec));
        return concrSuccStates.stream().map(s -> LazyState.of(s, initAbstractor)).collect(toList());
    }
}
