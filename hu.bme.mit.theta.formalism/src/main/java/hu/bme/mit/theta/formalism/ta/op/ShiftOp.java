package hu.bme.mit.theta.formalism.ta.op;

import hu.bme.mit.theta.core.type.RatType;
import hu.bme.mit.theta.formalism.common.decl.ClockDecl;
import hu.bme.mit.theta.formalism.common.stmt.AssignStmt;

public interface ShiftOp extends ClockOp {

	public ClockDecl getClock();

	public int getOffset();

	@Override
	public AssignStmt<RatType, RatType> toStmt();

}
