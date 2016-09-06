package hu.bme.mit.inf.theta.formalism.ta.op;

import hu.bme.mit.inf.theta.core.type.RatType;
import hu.bme.mit.inf.theta.formalism.common.decl.ClockDecl;
import hu.bme.mit.inf.theta.formalism.common.stmt.HavocStmt;

public interface FreeOp extends ClockOp {

	public ClockDecl getClock();

	@Override
	public HavocStmt<RatType> toStmt();

}
