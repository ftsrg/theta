package hu.bme.mit.theta.formalism.ta;

import hu.bme.mit.theta.formalism.common.Loc;
import hu.bme.mit.theta.formalism.ta.constr.ClockConstr;

public interface TaLoc extends Loc<TaLoc, TaEdge> {

	public ClockConstr getInvar();

}
