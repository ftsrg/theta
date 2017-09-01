package hu.bme.mit.theta.core.clock.op;

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
