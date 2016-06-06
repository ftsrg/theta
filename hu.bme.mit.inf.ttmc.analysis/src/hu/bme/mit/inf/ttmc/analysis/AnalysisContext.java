package hu.bme.mit.inf.ttmc.analysis;

import java.util.Collection;

public interface AnalysisContext<S extends State, Init, Trans, Target> {

	public Init getInitialization();

	public Collection<? extends Trans> getTransitions(S state);

	public Target getTarget();

}