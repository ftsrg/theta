package hu.bme.mit.theta.formalism.ta.op;

import hu.bme.mit.theta.core.stmt.AssumeStmt;
import hu.bme.mit.theta.formalism.ta.constr.ClockConstr;

public interface GuardOp extends ClockOp {

	ClockConstr getConstr();

	@Override
	AssumeStmt toStmt();

}
