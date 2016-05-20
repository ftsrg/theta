package hu.bme.mit.inf.ttmc.analysis.algorithm;

import java.util.List;
import java.util.Optional;

import hu.bme.mit.inf.ttmc.analysis.Precision;
import hu.bme.mit.inf.ttmc.analysis.State;

public interface Checker<S extends State, P extends Precision> {

	public Optional<List<S>> check(P precision);
}
