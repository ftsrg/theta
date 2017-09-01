package hu.bme.mit.theta.core.clock.op;

public interface ClockOpVisitor<P, R> {

	R visit(final CopyOp op, final P param);

	R visit(final FreeOp op, final P param);

	R visit(final GuardOp op, final P param);

	R visit(final ResetOp op, final P param);

	R visit(final ShiftOp op, final P param);

}
