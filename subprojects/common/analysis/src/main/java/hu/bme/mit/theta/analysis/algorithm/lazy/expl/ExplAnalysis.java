package hu.bme.mit.theta.analysis.algorithm.lazy.expl;

import hu.bme.mit.theta.analysis.*;
import hu.bme.mit.theta.analysis.expl.ExplOrd;
import hu.bme.mit.theta.analysis.expl.ExplState;
import hu.bme.mit.theta.analysis.unit.UnitPrec;
import hu.bme.mit.theta.core.model.Valuation;

import static com.google.common.base.Preconditions.checkNotNull;

public class ExplAnalysis<A extends Action> implements Analysis<ExplState, A, UnitPrec> {
    private final ExplInitFunc initFunc;
    private final ExplTransFunc<A> transFunc;

    private ExplAnalysis(final Valuation initialValuation, final ExplActionPost<A> explActionPost) {
        checkNotNull(initialValuation);
        checkNotNull(explActionPost);
        initFunc = ExplInitFunc.create(initialValuation);
        transFunc = ExplTransFunc.create(explActionPost);
    }

    public static <A extends Action> ExplAnalysis<A> create(final Valuation initialValuation, final ExplActionPost<A> explActionPost) {
        return new ExplAnalysis(initialValuation, explActionPost);
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
