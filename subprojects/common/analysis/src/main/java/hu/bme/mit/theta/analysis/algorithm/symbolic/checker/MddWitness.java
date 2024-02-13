package hu.bme.mit.theta.analysis.algorithm.symbolic.checker;

import hu.bme.mit.delta.java.mdd.MddHandle;
import hu.bme.mit.delta.mdd.MddInterpreter;
import hu.bme.mit.theta.analysis.algorithm.Witness;

public class MddWitness implements Witness {

    private final MddHandle stateSpace;

    private MddWitness(MddHandle stateSpace) {
        this.stateSpace = stateSpace;
    }

    public static MddWitness of(MddHandle stateSpace){
        return new MddWitness(stateSpace);
    }

    public Long size(){
        return MddInterpreter.calculateNonzeroCount(stateSpace);
    }
}
