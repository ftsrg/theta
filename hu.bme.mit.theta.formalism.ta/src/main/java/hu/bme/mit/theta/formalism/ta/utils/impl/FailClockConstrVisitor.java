package hu.bme.mit.theta.formalism.ta.utils.impl;

import hu.bme.mit.theta.formalism.ta.constr.AndConstr;
import hu.bme.mit.theta.formalism.ta.constr.DiffEqConstr;
import hu.bme.mit.theta.formalism.ta.constr.DiffGeqConstr;
import hu.bme.mit.theta.formalism.ta.constr.DiffGtConstr;
import hu.bme.mit.theta.formalism.ta.constr.DiffLeqConstr;
import hu.bme.mit.theta.formalism.ta.constr.DiffLtConstr;
import hu.bme.mit.theta.formalism.ta.constr.FalseConstr;
import hu.bme.mit.theta.formalism.ta.constr.TrueConstr;
import hu.bme.mit.theta.formalism.ta.constr.UnitEqConstr;
import hu.bme.mit.theta.formalism.ta.constr.UnitGeqConstr;
import hu.bme.mit.theta.formalism.ta.constr.UnitGtConstr;
import hu.bme.mit.theta.formalism.ta.constr.UnitLeqConstr;
import hu.bme.mit.theta.formalism.ta.constr.UnitLtConstr;
import hu.bme.mit.theta.formalism.ta.utils.ClockConstrVisitor;

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
