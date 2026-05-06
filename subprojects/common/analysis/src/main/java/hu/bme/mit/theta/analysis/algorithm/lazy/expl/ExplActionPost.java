package hu.bme.mit.theta.analysis.algorithm.lazy.expl;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.expl.ExplState;

public interface ExplActionPost<A extends Action> {
    ExplState post(final ExplState state, final A action);
}
