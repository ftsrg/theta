package hu.bme.mit.theta.analysis.algorithm.symbolic.checker;

import hu.bme.mit.delta.java.mdd.MddHandle;
import hu.bme.mit.delta.mdd.MddInterpreter;
import hu.bme.mit.theta.analysis.Cex;

public class MddCex implements Cex {

    private final MddHandle violatingStates;

    private MddCex(MddHandle violatingStates) {
        this.violatingStates = violatingStates;
    }

    public static MddCex of(MddHandle violatingStates){
        return new MddCex(violatingStates);
    }

    @Override
    public int length() {
        return -1;
    }

    public Long size() {
        return MddInterpreter.calculateNonzeroCount(violatingStates);
    }
}
