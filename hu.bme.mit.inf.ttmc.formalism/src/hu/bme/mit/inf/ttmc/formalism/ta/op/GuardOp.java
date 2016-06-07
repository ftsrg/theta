package hu.bme.mit.inf.ttmc.formalism.ta.op;

import hu.bme.mit.inf.ttmc.formalism.common.stmt.AssumeStmt;
import hu.bme.mit.inf.ttmc.formalism.ta.constr.ClockConstr;

public interface GuardOp extends ClockOp {

	public ClockConstr getConstr();

	@Override
	public AssumeStmt toStmt();

}
