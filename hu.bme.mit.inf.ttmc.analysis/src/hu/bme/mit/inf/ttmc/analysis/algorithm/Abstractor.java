package hu.bme.mit.inf.ttmc.analysis.algorithm;

import hu.bme.mit.inf.ttmc.analysis.Action;
import hu.bme.mit.inf.ttmc.analysis.Precision;
import hu.bme.mit.inf.ttmc.analysis.State;

public interface Abstractor<S extends State, A extends Action, P extends Precision> {

	public ARG<S, A> getARG();

	public void init(final P precision);

	public void check(final P precision);

}
