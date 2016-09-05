package hu.bme.mit.inf.theta.formalism.tcfa;

import java.util.Collection;

import hu.bme.mit.inf.theta.formalism.common.automaton.Automaton;
import hu.bme.mit.inf.theta.formalism.common.decl.ClockDecl;
import hu.bme.mit.inf.theta.formalism.common.decl.VarDecl;

public interface TCFA extends Automaton<TcfaLoc, TcfaEdge> {

	public Collection<? extends VarDecl<?>> getDataVars();

	public Collection<? extends ClockDecl> getClockVars();

}