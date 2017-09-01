package hu.bme.mit.theta.core.clock.constr;

public class FailClockConstrVisitor<P, R> implements ClockConstrVisitor<P, R> {

	@Override
	public R visit(final TrueConstr constr, final P param) {
		throw new UnsupportedOperationException();
	}

	@Override
	public R visit(final FalseConstr constr, final P param) {
		throw new UnsupportedOperationException();
	}

	@Override
	public R visit(final UnitLtConstr constr, final P param) {
		throw new UnsupportedOperationException();
	}

	@Override
	public R visit(final UnitLeqConstr constr, final P param) {
		throw new UnsupportedOperationException();
	}

	@Override
	public R visit(final UnitGtConstr constr, final P param) {
		throw new UnsupportedOperationException();
	}

	@Override
	public R visit(final UnitGeqConstr constr, final P param) {
		throw new UnsupportedOperationException();
	}

	@Override
	public R visit(final UnitEqConstr constr, final P param) {
		throw new UnsupportedOperationException();
	}

	@Override
	public R visit(final DiffLtConstr constr, final P param) {
		throw new UnsupportedOperationException();
	}

	@Override
	public R visit(final DiffLeqConstr constr, final P param) {
		throw new UnsupportedOperationException();
	}

	@Override
	public R visit(final DiffGtConstr constr, final P param) {
		throw new UnsupportedOperationException();
	}

	@Override
	public R visit(final DiffGeqConstr constr, final P param) {
		throw new UnsupportedOperationException();
	}

	@Override
	public R visit(final DiffEqConstr constr, final P param) {
		throw new UnsupportedOperationException();
	}

	@Override
	public R visit(final AndConstr constr, final P param) {
		throw new UnsupportedOperationException();
	}

}
