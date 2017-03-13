package hu.bme.mit.theta.formalism.ta.utils.impl;

import hu.bme.mit.theta.formalism.ta.op.CopyOp;
import hu.bme.mit.theta.formalism.ta.op.FreeOp;
import hu.bme.mit.theta.formalism.ta.op.GuardOp;
import hu.bme.mit.theta.formalism.ta.op.ResetOp;
import hu.bme.mit.theta.formalism.ta.op.ShiftOp;
import hu.bme.mit.theta.formalism.ta.utils.ClockOpVisitor;

public class FailClockOpVisitor<P, R> implements ClockOpVisitor<P, R> {

	@Override
	public R visit(final CopyOp op, final P param) {
		throw new UnsupportedOperationException();
	}

	@Override
	public R visit(final FreeOp op, final P param) {
		throw new UnsupportedOperationException();
	}

	@Override
	public R visit(final GuardOp op, final P param) {
		throw new UnsupportedOperationException();
	}

	@Override
	public R visit(final ResetOp op, final P param) {
		throw new UnsupportedOperationException();
	}

	@Override
	public R visit(final ShiftOp op, final P param) {
		throw new UnsupportedOperationException();
	}

}
