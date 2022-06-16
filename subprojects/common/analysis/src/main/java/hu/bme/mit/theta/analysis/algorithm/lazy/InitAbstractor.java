package hu.bme.mit.theta.analysis.algorithm.lazy;

import hu.bme.mit.theta.analysis.State;

@FunctionalInterface
public interface InitAbstractor<SConcr extends State, SAbstr extends State> {

    SAbstr getInitAbstrState(final SConcr state);

}
