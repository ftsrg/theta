package hu.bme.mit.theta.analysis.multi;

import hu.bme.mit.theta.analysis.State;

public final class NextSideFunctions {

    
    public static <L extends State, R extends State, D extends State> MultiSourceSide alternating(MultiState<L, R, D> state) {
        return state.getSourceSide() == MultiSourceSide.LEFT ? MultiSourceSide.RIGHT : MultiSourceSide.LEFT;
    }

}
