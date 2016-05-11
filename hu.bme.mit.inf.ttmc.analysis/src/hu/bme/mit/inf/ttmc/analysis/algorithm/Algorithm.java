package hu.bme.mit.inf.ttmc.analysis.algorithm;

import java.util.Collection;

import hu.bme.mit.inf.ttmc.analysis.Precision;
import hu.bme.mit.inf.ttmc.analysis.State;

public interface Algorithm<S extends State, P extends Precision> {

	public Collection<S> run(P precision);

}
