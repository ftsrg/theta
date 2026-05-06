package hu.bme.mit.theta.analysis.algorithm.lazy.expl;

import hu.bme.mit.theta.analysis.InitFunc;
import hu.bme.mit.theta.analysis.expl.ExplState;
import hu.bme.mit.theta.analysis.unit.UnitPrec;
import hu.bme.mit.theta.core.model.Valuation;

import java.util.Collection;

import static com.google.common.base.Preconditions.checkNotNull;
import static java.util.Collections.singleton;

final class ExplInitFunc implements InitFunc<ExplState, UnitPrec> {

    private final Valuation initialValuation;

    private ExplInitFunc(final Valuation initialValuation) {
        this.initialValuation = checkNotNull(initialValuation);
    }

    public static ExplInitFunc create(final Valuation initialValuation) {
        return new ExplInitFunc(initialValuation);
    }

    @Override
    public Collection<ExplState> getInitStates(final UnitPrec prec) {
        checkNotNull(prec);
        final ExplState initState = ExplState.of(initialValuation);
        return singleton(initState);
    }

}