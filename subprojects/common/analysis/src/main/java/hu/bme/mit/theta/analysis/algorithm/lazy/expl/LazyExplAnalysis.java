package hu.bme.mit.theta.analysis.algorithm.lazy.expl;

import hu.bme.mit.theta.analysis.*;
import hu.bme.mit.theta.analysis.expl.ExplOrd;
import hu.bme.mit.theta.analysis.expl.ExplState;
import hu.bme.mit.theta.analysis.unit.UnitPrec;
import hu.bme.mit.theta.core.model.Valuation;

import static com.google.common.base.Preconditions.checkNotNull;

public class LazyExplAnalysis<A extends Action> implements Analysis<ExplState, A, UnitPrec> {
    private final LazyExplInitFunc initFunc;
    private final LazyExplTransFunc<A> transFunc;

    private LazyExplAnalysis(final Valuation initialValuation, final ExplPost<A> explPost) {
        checkNotNull(initialValuation);
        checkNotNull(explPost);
        initFunc = LazyExplInitFunc.create(initialValuation);
        transFunc = LazyExplTransFunc.create(explPost);
    }

    public static <A extends Action> LazyExplAnalysis<A> create(final Valuation initialValuation, final ExplPost<A> explPost) {
        return new LazyExplAnalysis<>(initialValuation, explPost);
    }

    @Override
    public PartialOrd<ExplState> getPartialOrd() {
        return ExplOrd.getInstance();
    }

    @Override
    public InitFunc<ExplState, UnitPrec> getInitFunc() {
        return initFunc;
    }

    @Override
    public TransFunc<ExplState, A, UnitPrec> getTransFunc() {
        return transFunc;
    }
}
