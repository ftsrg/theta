package hu.bme.mit.theta.formalism.tcfa;

import java.util.Collection;

import hu.bme.mit.theta.formalism.common.Automaton;
import hu.bme.mit.theta.formalism.common.decl.ClockDecl;
import hu.bme.mit.theta.formalism.common.decl.VarDecl;

public interface TCFA extends Automaton<TcfaLoc, TcfaEdge> {

	public Collection<? extends VarDecl<?>> getDataVars();

	public Collection<? extends ClockDecl> getClockVars();

}