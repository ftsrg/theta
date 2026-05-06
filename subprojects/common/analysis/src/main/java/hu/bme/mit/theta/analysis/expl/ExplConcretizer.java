package hu.bme.mit.theta.analysis.expl;

import hu.bme.mit.theta.analysis.PartialOrd;
import hu.bme.mit.theta.analysis.algorithm.lazy.itp.Concretizer;

public final class ExplConcretizer implements Concretizer<ExplState, ExplState> {

    private final static ExplConcretizer INSTANCE = new ExplConcretizer();

    private final PartialOrd<ExplState> ord;

    private ExplConcretizer() {
        ord = ExplOrd.getInstance();
    }

    public static ExplConcretizer getInstance() {
        return INSTANCE;
    }

    @Override
    public ExplState concretize(final ExplState state) {
        return state;
    }

    @Override
    public boolean proves(final ExplState state1, final ExplState state2) {
        return ord.isLeq(state1, state2);
    }

    @Override
    public boolean inconsistentConcrState(final ExplState state) {
        return state.isBottom();
    }
}
