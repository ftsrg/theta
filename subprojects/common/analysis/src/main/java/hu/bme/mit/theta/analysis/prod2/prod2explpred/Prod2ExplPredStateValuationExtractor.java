package hu.bme.mit.theta.analysis.prod2.prod2explpred;

import hu.bme.mit.theta.analysis.expl.ExplState;
import hu.bme.mit.theta.analysis.expl.ExplStateValuationExtractor;
import hu.bme.mit.theta.analysis.pred.PredState;
import hu.bme.mit.theta.analysis.prod2.Prod2State;
import hu.bme.mit.theta.analysis.utils.ValuationExtractor;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.model.Valuation;

import java.util.Collection;

public class Prod2ExplPredStateValuationExtractor implements ValuationExtractor<Prod2State<ExplState, PredState>> {

    private final ExplStateValuationExtractor explValExtractor;

    private Prod2ExplPredStateValuationExtractor(final ExplStateValuationExtractor explValExtractor) {
        this.explValExtractor = explValExtractor;
    }

    public static Prod2ExplPredStateValuationExtractor create(final ExplStateValuationExtractor explStateValExtractor) {
        return new Prod2ExplPredStateValuationExtractor(explStateValExtractor);
    }

    @Override
    public Valuation extractValuation(Prod2State<ExplState, PredState> state) {
        final ExplState explState = state.getState1();
        return explValExtractor.extractValuation(explState);
    }

    @Override
    public Valuation extractValuationForVars(Prod2State<ExplState, PredState> state, Collection<VarDecl<?>> vars) {
        final ExplState explState = state.getState1();
        return explValExtractor.extractValuationForVars(explState, vars);
    }
}
