package hu.bme.mit.theta.analysis.algorithm.lazy;

import hu.bme.mit.theta.analysis.State;

public interface Concretizer<S1 extends State, S2 extends State> {

    S2 concretize(final S1 state);

    boolean proves(final S1 state1, final S2 state2);

}
