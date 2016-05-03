package hu.bme.mit.inf.ttmc.formalism.ta;

import hu.bme.mit.inf.ttmc.formalism.common.automaton.Loc;
import hu.bme.mit.inf.ttmc.formalism.ta.constr.Constr;

public interface TALoc extends Loc<TALoc, TAEdge> {

	public Constr getInvar();

}
