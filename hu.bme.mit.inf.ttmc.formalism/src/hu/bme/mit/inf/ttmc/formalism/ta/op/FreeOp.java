package hu.bme.mit.inf.ttmc.formalism.ta.op;

import hu.bme.mit.inf.ttmc.core.type.RatType;
import hu.bme.mit.inf.ttmc.formalism.common.decl.ClockDecl;
import hu.bme.mit.inf.ttmc.formalism.common.stmt.HavocStmt;

public interface FreeOp extends ClockOp {

	public ClockDecl getClock();

	@Override
	public HavocStmt<RatType> toStmt();

}
