package hu.bme.mit.inf.ttmc.analysis;

import java.util.Collection;

public interface AnalysisContext<S extends State, A extends Action> {

	public Collection<? extends A> getEnabledActionsFor(S state);

}