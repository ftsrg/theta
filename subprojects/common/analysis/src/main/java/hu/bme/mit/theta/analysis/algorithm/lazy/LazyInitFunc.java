package hu.bme.mit.theta.analysis.algorithm.lazy;

import hu.bme.mit.theta.analysis.InitFunc;
import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.expr.ExprState;

import java.util.ArrayList;
import java.util.Collection;

import static com.google.common.base.Preconditions.checkNotNull;
import static java.util.stream.Collectors.toList;

public final class LazyInitFunc<SConcr extends State, SAbstr extends ExprState, P extends Prec> implements InitFunc<LazyState<SConcr, SAbstr>, P> {

    private final InitFunc<SConcr, P> concrInitFunc;
    private final InitAbstractor<SConcr, SAbstr> initAbstractor;

    private LazyInitFunc(final InitFunc<SConcr, P> concrInitFunc, final InitAbstractor<SConcr, SAbstr> initAbstractor) {
        this.concrInitFunc = checkNotNull(concrInitFunc);
        this.initAbstractor = checkNotNull(initAbstractor);
    }

    public static <SConcr extends State, SAbstr extends ExprState, P extends Prec> LazyInitFunc<SConcr, SAbstr, P>
    create(final InitFunc<SConcr, P> concrInitFunc, final InitAbstractor<SConcr, SAbstr> initAbstractor) {
        return new LazyInitFunc<>(concrInitFunc, initAbstractor);
    }

    @Override
    public Collection<? extends LazyState<SConcr, SAbstr>> getInitStates(P prec) {
        final Collection<SConcr> concrInitStates = new ArrayList<>(concrInitFunc.getInitStates(prec));
        return concrInitStates.stream().map(s -> LazyState.of(s, initAbstractor)).collect(toList());
    }
}
