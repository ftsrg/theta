package hu.bme.mit.inf.ttmc.analysis.algorithm;

import hu.bme.mit.inf.ttmc.analysis.Counterexample;
import hu.bme.mit.inf.ttmc.analysis.Precision;
import hu.bme.mit.inf.ttmc.analysis.expl.ExplState;

public interface CEGARLoop<P extends Precision> {

	CEGARStatus check(final P initPrecision);

	CEGARStatus getStatus();

	Counterexample<ExplState> getCounterexample();
}
