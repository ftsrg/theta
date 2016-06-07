package hu.bme.mit.inf.ttmc.formalism.ta.op.impl;

import hu.bme.mit.inf.ttmc.formalism.common.decl.ClockDecl;
import hu.bme.mit.inf.ttmc.formalism.common.stmt.Stmt;
import hu.bme.mit.inf.ttmc.formalism.ta.constr.ClockConstr;
import hu.bme.mit.inf.ttmc.formalism.ta.op.ClockOp;
import hu.bme.mit.inf.ttmc.formalism.ta.op.CopyOp;
import hu.bme.mit.inf.ttmc.formalism.ta.op.FreeOp;
import hu.bme.mit.inf.ttmc.formalism.ta.op.GuardOp;
import hu.bme.mit.inf.ttmc.formalism.ta.op.ResetOp;
import hu.bme.mit.inf.ttmc.formalism.ta.op.ShiftOp;

public final class ClockOps {

	private ClockOps() {
	}

	////

	public static ClockOp fromStmt(final Stmt stmt) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

	////

	public static CopyOp Copy(final ClockDecl clock, final ClockDecl value) {
		return new CopyOpImpl(clock, value);
	}

	public static FreeOp Free(final ClockDecl clock) {
		return new FreeOpImpl(clock);
	}

	public static GuardOp Guard(final ClockConstr constr) {
		return new GuardOpImpl(constr);
	}

	public static ResetOp Reset(final ClockDecl clock, final int value) {
		return new ResetOpImpl(clock, value);
	}

	public static ShiftOp Shift(final ClockDecl clock, final int offset) {
		return new ShifOpImpl(clock, offset);
	}

}
