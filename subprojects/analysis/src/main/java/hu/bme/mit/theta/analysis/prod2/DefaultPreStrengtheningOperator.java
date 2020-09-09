package hu.bme.mit.theta.analysis.prod2;

import hu.bme.mit.theta.analysis.State;

import static com.google.common.base.Preconditions.checkNotNull;

public final class DefaultPreStrengtheningOperator<S1 extends State, S2 extends State> implements PreStrengtheningOperator<S1, S2> {

    private DefaultPreStrengtheningOperator(){}

    public static <S1 extends State, S2 extends State> PreStrengtheningOperator<S1, S2> create(){
        return new DefaultPreStrengtheningOperator<>();
    }

    @Override
    public S1 strengthenState1(Prod2State<S1, S2> state) {
        checkNotNull(state);

        return state.getState1();
    }

    @Override
    public S2 strengthenState2(Prod2State<S1, S2> state) {
        checkNotNull(state);

        return state.getState2();
    }
}
