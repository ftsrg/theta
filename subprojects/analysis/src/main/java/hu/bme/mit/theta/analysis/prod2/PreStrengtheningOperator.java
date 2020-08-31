package hu.bme.mit.theta.analysis.prod2;

import hu.bme.mit.theta.analysis.State;

public interface PreStrengtheningOperator<S1 extends State, S2 extends State> {

    S1 strengthenState1(final Prod2State<S1, S2> state);

    S2 strengthenState2(final Prod2State<S1, S2> state);

}
