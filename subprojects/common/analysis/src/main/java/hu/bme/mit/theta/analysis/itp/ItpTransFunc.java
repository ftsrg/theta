package hu.bme.mit.theta.analysis.itp;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.TransFunc;
import hu.bme.mit.theta.analysis.algorithm.lazy.InitAbstractor;
import hu.bme.mit.theta.analysis.expr.ExprState;

import java.util.ArrayList;
import java.util.Collection;

import static com.google.common.base.Preconditions.checkNotNull;
import static java.util.stream.Collectors.toList;

public final class ItpTransFunc<SConcr extends State, SAbstr extends ExprState, A extends Action, P extends Prec> implements TransFunc<ItpState<SConcr, SAbstr>, A, P> {

    private final TransFunc<SConcr, A, P> concrTransFunc;
    private final InitAbstractor<SConcr, SAbstr> initAbstractor;

    private ItpTransFunc(final TransFunc<SConcr, A, P> concrTransFunc, final InitAbstractor<SConcr, SAbstr> initAbstractor){
        this.concrTransFunc = checkNotNull(concrTransFunc);
        this.initAbstractor = checkNotNull(initAbstractor);
    }

    public static <SConcr extends State, SAbstr extends ExprState, A extends Action, P extends Prec> ItpTransFunc<SConcr, SAbstr, A, P>
    create(final TransFunc<SConcr, A, P> concrTransFunc, final InitAbstractor<SConcr, SAbstr> initAbstractor) {
        return new ItpTransFunc<>(concrTransFunc, initAbstractor);
    }

    @Override
    public Collection<? extends ItpState<SConcr, SAbstr>> getSuccStates(ItpState<SConcr, SAbstr> state, A action, P prec) {
        final SConcr concrState = state.getConcrState();
        final Collection<SConcr> concrSuccStates = new ArrayList<>(concrTransFunc.getSuccStates(concrState, action, prec));
        return concrSuccStates.stream().map(s -> ItpState.of(s, initAbstractor)).collect(toList());
    }
}
