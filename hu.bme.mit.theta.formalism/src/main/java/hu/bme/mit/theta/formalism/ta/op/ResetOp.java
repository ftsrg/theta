package hu.bme.mit.theta.formalism.ta.op;

import hu.bme.mit.theta.core.type.IntType;
import hu.bme.mit.theta.core.type.RatType;
import hu.bme.mit.theta.formalism.common.decl.ClockDecl;
import hu.bme.mit.theta.formalism.common.stmt.AssignStmt;

public interface ResetOp extends ClockOp {

	public ClockDecl getClock();

	public int getValue();

	@Override
	public AssignStmt<RatType, IntType> toStmt();

}
