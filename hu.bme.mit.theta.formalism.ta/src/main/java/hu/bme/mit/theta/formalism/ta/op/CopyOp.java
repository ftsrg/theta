package hu.bme.mit.theta.formalism.ta.op;

import hu.bme.mit.theta.core.stmt.AssignStmt;
import hu.bme.mit.theta.core.type.RatType;
import hu.bme.mit.theta.formalism.ta.decl.ClockDecl;

public interface CopyOp extends ClockOp {

	ClockDecl getClock();

	ClockDecl getValue();

	@Override
	AssignStmt<RatType, RatType> toStmt();

}
