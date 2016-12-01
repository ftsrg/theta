package hu.bme.mit.theta.formalism.tcfa;

import java.util.Collection;

import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.formalism.common.Automaton;
import hu.bme.mit.theta.formalism.common.decl.ClockDecl;

public interface TCFA extends Automaton<TcfaLoc, TcfaEdge> {

	Collection<? extends VarDecl<?>> getDataVars();

	Collection<? extends ClockDecl> getClockVars();

}