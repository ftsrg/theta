package hu.bme.mit.theta.formalism.ta.op;

import hu.bme.mit.theta.core.stmt.HavocStmt;
import hu.bme.mit.theta.core.type.RatType;
import hu.bme.mit.theta.formalism.ta.decl.ClockDecl;

public interface FreeOp extends ClockOp {

	ClockDecl getClock();

	@Override
	HavocStmt<RatType> toStmt();

}
