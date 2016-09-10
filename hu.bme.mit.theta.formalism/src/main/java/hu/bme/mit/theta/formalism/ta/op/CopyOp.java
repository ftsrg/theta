package hu.bme.mit.theta.formalism.ta.op;

import hu.bme.mit.theta.core.type.RatType;
import hu.bme.mit.theta.formalism.common.decl.ClockDecl;
import hu.bme.mit.theta.formalism.common.stmt.AssignStmt;

public interface CopyOp extends ClockOp {

	public ClockDecl getClock();

	public ClockDecl getValue();

	@Override
	public AssignStmt<RatType, RatType> toStmt();

}
