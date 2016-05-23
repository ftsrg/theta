package hu.bme.mit.inf.ttmc.analysis.concr;

import hu.bme.mit.inf.ttmc.analysis.Counterexample;
import hu.bme.mit.inf.ttmc.analysis.State;
import hu.bme.mit.inf.ttmc.analysis.expl.ExplState;
import hu.bme.mit.inf.ttmc.formalism.Formalism;

public interface Concretizer<F extends Formalism, S extends State> {

	public boolean check(Counterexample<? extends S> abstractCex);

	public Counterexample<ExplState> getConcreteCex();

	public Counterexample<ExplState> getPrefix();

	public void setGenPrefix(boolean genPrefix);

	public boolean getGenPrefix();

}
