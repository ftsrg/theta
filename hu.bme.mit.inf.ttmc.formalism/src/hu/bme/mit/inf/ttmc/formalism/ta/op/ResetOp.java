package hu.bme.mit.inf.ttmc.formalism.ta.op;

import hu.bme.mit.inf.ttmc.core.type.IntType;
import hu.bme.mit.inf.ttmc.core.type.RatType;
import hu.bme.mit.inf.ttmc.formalism.common.decl.ClockDecl;
import hu.bme.mit.inf.ttmc.formalism.common.stmt.AssignStmt;

public interface ResetOp extends ClockOp {

	public ClockDecl getClock();

	public int getValue();

	@Override
	public AssignStmt<RatType, IntType> toStmt();

}
