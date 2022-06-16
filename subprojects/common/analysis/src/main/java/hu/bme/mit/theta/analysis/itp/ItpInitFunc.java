package hu.bme.mit.theta.analysis.itp;

import hu.bme.mit.theta.analysis.InitFunc;
import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.algorithm.lazy.InitAbstractor;
import hu.bme.mit.theta.analysis.expr.ExprState;

import java.util.ArrayList;
import java.util.Collection;

import static com.google.common.base.Preconditions.checkNotNull;
import static java.util.stream.Collectors.toList;

public class ItpInitFunc<SConcr extends State, SAbstr extends ExprState, P extends Prec> implements InitFunc<ItpState<SConcr, SAbstr>, P> {

    private final InitFunc<SConcr, P> concrInitFunc;
    private final InitAbstractor<SConcr, SAbstr> initAbstractor;

    private ItpInitFunc(final InitFunc<SConcr, P> concrInitFunc, final InitAbstractor<SConcr, SAbstr> initAbstractor) {
        this.concrInitFunc = checkNotNull(concrInitFunc);
        this.initAbstractor = checkNotNull(initAbstractor);
    }

    public static <SConcr extends State, SAbstr extends ExprState, P extends Prec> ItpInitFunc<SConcr, SAbstr, P>
    create(final InitFunc<SConcr, P> concrInitFunc, final InitAbstractor<SConcr, SAbstr> initAbstractor) {
        return new ItpInitFunc<>(concrInitFunc, initAbstractor);
    }

    @Override
    public Collection<? extends ItpState<SConcr, SAbstr>> getInitStates(P prec) {
        final Collection<SConcr> concrInitStates = new ArrayList<>(concrInitFunc.getInitStates(prec));
        return concrInitStates.stream().map(s -> ItpState.of(s, initAbstractor)).collect(toList());
    }
}
