package hu.bme.mit.inf.theta.formalism.ta;

import hu.bme.mit.inf.theta.formalism.common.automaton.Loc;
import hu.bme.mit.inf.theta.formalism.ta.constr.ClockConstr;

public interface TaLoc extends Loc<TaLoc, TaEdge> {

	public ClockConstr getInvar();

}
