package hu.bme.mit.inf.ttmc.formalism.ta;

import hu.bme.mit.inf.ttmc.formalism.common.automaton.Loc;
import hu.bme.mit.inf.ttmc.formalism.ta.constr.ClockConstr;

public interface TALoc extends Loc<TALoc, TAEdge> {

	public ClockConstr getInvar();

}
