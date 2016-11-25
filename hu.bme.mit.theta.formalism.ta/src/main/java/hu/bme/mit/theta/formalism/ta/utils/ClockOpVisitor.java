package hu.bme.mit.theta.formalism.ta.utils;

import hu.bme.mit.theta.formalism.ta.op.CopyOp;
import hu.bme.mit.theta.formalism.ta.op.FreeOp;
import hu.bme.mit.theta.formalism.ta.op.GuardOp;
import hu.bme.mit.theta.formalism.ta.op.ResetOp;
import hu.bme.mit.theta.formalism.ta.op.ShiftOp;

public interface ClockOpVisitor<P, R> {

	R visit(final CopyOp op, final P param);

	R visit(final FreeOp op, final P param);

	R visit(final GuardOp op, final P param);

	R visit(final ResetOp op, final P param);

	R visit(final ShiftOp op, final P param);

}
