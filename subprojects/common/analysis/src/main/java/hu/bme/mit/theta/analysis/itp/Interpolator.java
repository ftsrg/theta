package hu.bme.mit.theta.analysis.itp;

import hu.bme.mit.theta.analysis.State;

import java.util.Collection;

public interface Interpolator<SAbstr extends State, SItp extends State> {

    SItp toItpDom(final SAbstr state);

    SAbstr interpolate(final SAbstr state1, final SItp state2);

    boolean refutes(final SAbstr state1, final SItp state2);

    Collection<SItp> complement(final SItp state);

}
