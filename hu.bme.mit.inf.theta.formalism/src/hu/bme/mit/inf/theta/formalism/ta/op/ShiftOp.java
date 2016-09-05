package hu.bme.mit.inf.theta.formalism.ta.op;

import hu.bme.mit.inf.theta.core.type.RatType;
import hu.bme.mit.inf.theta.formalism.common.decl.ClockDecl;
import hu.bme.mit.inf.theta.formalism.common.stmt.AssignStmt;

public interface ShiftOp extends ClockOp {

	public ClockDecl getClock();

	public int getOffset();

	@Override
	public AssignStmt<RatType, RatType> toStmt();

}
