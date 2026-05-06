package hu.bme.mit.theta.analysis.algorithm.lazy.itp;

import hu.bme.mit.theta.analysis.State;

public interface Concretizer<SConcr extends State, SAbstr extends State> {

    SAbstr concretize(final SConcr state);

    boolean proves(final SConcr state1, final SAbstr state2);

    boolean inconsistentConcrState(final SConcr state);

}
