package hu.bme.mit.inf.ttmc.formalism.ta.utils;

import hu.bme.mit.inf.ttmc.formalism.ta.op.CopyOp;
import hu.bme.mit.inf.ttmc.formalism.ta.op.FreeOp;
import hu.bme.mit.inf.ttmc.formalism.ta.op.GuardOp;
import hu.bme.mit.inf.ttmc.formalism.ta.op.ResetOp;
import hu.bme.mit.inf.ttmc.formalism.ta.op.ShiftOp;

public interface ClockOpVisitor<P, R> {

	public R visit(final CopyOp op, final P param);

	public R visit(final FreeOp op, final P param);

	public R visit(final GuardOp op, final P param);

	public R visit(final ResetOp op, final P param);

	public R visit(final ShiftOp op, final P param);

}
