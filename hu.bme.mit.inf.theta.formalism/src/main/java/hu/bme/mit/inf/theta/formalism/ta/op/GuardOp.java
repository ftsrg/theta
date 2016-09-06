package hu.bme.mit.inf.theta.formalism.ta.op;

import hu.bme.mit.inf.theta.formalism.common.stmt.AssumeStmt;
import hu.bme.mit.inf.theta.formalism.ta.constr.ClockConstr;

public interface GuardOp extends ClockOp {

	public ClockConstr getConstr();

	@Override
	public AssumeStmt toStmt();

}
