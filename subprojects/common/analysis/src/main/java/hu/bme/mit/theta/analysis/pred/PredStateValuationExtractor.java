package hu.bme.mit.theta.analysis.pred;

import hu.bme.mit.theta.analysis.utils.ValuationExtractor;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.model.ImmutableValuation;
import hu.bme.mit.theta.core.model.Valuation;

import java.util.Collection;

public final class PredStateValuationExtractor implements ValuationExtractor<PredState> {

    private static final class LazyHolder {
        private static final PredStateValuationExtractor INSTANCE = new PredStateValuationExtractor();
    }

    private PredStateValuationExtractor() {
    }

    public static PredStateValuationExtractor getInstance() {
        return PredStateValuationExtractor.LazyHolder.INSTANCE;
    }


    @Override
    public Valuation extractValuation(PredState state) {
        return ImmutableValuation.empty();
    }

    @Override
    public Valuation extractValuationForVars(PredState state, Collection<VarDecl<?>> vars) {
        return ImmutableValuation.empty();
    }
}
