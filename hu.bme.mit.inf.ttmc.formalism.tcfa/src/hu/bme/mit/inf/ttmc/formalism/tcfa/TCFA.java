package hu.bme.mit.inf.ttmc.formalism.tcfa;

import java.util.Collection;

import hu.bme.mit.inf.ttmc.formalism.common.automaton.Automaton;
import hu.bme.mit.inf.ttmc.formalism.common.decl.ClockDecl;
import hu.bme.mit.inf.ttmc.formalism.common.decl.VarDecl;

public interface TCFA extends Automaton<TCFALoc, TCFAEdge> {

	public Collection<? extends VarDecl<?>> getDataVars();

	public Collection<? extends ClockDecl> getClockVars();

}