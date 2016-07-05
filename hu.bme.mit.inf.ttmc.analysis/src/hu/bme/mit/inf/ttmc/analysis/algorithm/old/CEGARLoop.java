package hu.bme.mit.inf.ttmc.analysis.algorithm.old;

import hu.bme.mit.inf.ttmc.analysis.Counterexample;
import hu.bme.mit.inf.ttmc.analysis.Precision;
import hu.bme.mit.inf.ttmc.analysis.expl.ExplState;

public interface CEGARLoop<P extends Precision> {
	boolean check(P initPrecision);

	Counterexample<ExplState> getConcreteCex();
}
