package hu.bme.mit.inf.ttmc.formalism.ta.constr.impl;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;

import com.google.common.collect.ImmutableSet;

import hu.bme.mit.inf.ttmc.formalism.ta.constr.AndConstr;
import hu.bme.mit.inf.ttmc.formalism.ta.constr.Clock;
import hu.bme.mit.inf.ttmc.formalism.ta.constr.Constr;
import hu.bme.mit.inf.ttmc.formalism.ta.constr.DiffEqConstr;
import hu.bme.mit.inf.ttmc.formalism.ta.constr.DiffGeqConstr;
import hu.bme.mit.inf.ttmc.formalism.ta.constr.DiffGtConstr;
import hu.bme.mit.inf.ttmc.formalism.ta.constr.DiffLeqConstr;
import hu.bme.mit.inf.ttmc.formalism.ta.constr.DiffLtConstr;
import hu.bme.mit.inf.ttmc.formalism.ta.constr.TrueConstr;
import hu.bme.mit.inf.ttmc.formalism.ta.constr.UnitEqConstr;
import hu.bme.mit.inf.ttmc.formalism.ta.constr.UnitGeqConstr;
import hu.bme.mit.inf.ttmc.formalism.ta.constr.UnitGtConstr;
import hu.bme.mit.inf.ttmc.formalism.ta.constr.UnitLeqConstr;
import hu.bme.mit.inf.ttmc.formalism.ta.constr.UnitLtConstr;

public final class Constrs {

	private Constrs() {
	}

	private static final TrueConstr TRUE_CONSTR;

	static {
		TRUE_CONSTR = new TrueConstrImpl();
	}

	public static Clock Clock(final String name) {
		checkNotNull(name);
		checkArgument(name.length() > 0);
		return new ClockImpl(name);
	}

	public static TrueConstr True() {
		return TRUE_CONSTR;
	}

	public static UnitLtConstr Lt(final Clock clock, final int bound) {
		checkNotNull(clock);
		return new UnitLtConstrImpl(clock, bound);
	}

	public static UnitLeqConstr Leq(final Clock clock, final int bound) {
		checkNotNull(clock);
		return new UnitLeqConstrImpl(clock, bound);
	}

	public static UnitGtConstr Gt(final Clock clock, final int bound) {
		checkNotNull(clock);
		return new UnitGtConstrImpl(clock, bound);
	}

	public static UnitGeqConstr Geq(final Clock clock, final int bound) {
		checkNotNull(clock);
		return new UnitGeqConstrImpl(clock, bound);
	}

	public static UnitEqConstr Eq(final Clock clock, final int bound) {
		checkNotNull(clock);
		return new UnitEqConstrImpl(clock, bound);
	}

	public static DiffLtConstr Lt(final Clock leftClock, final Clock rightClock, final int bound) {
		checkNotNull(leftClock);
		checkNotNull(rightClock);
		return new DiffLtConstrImpl(leftClock, rightClock, bound);
	}

	public static DiffLeqConstr Leq(final Clock leftClock, final Clock rightClock, final int bound) {
		checkNotNull(leftClock);
		checkNotNull(rightClock);
		return new DiffLeqConstrImpl(leftClock, rightClock, bound);
	}

	public static DiffGtConstr Gt(final Clock leftClock, final Clock rightClock, final int bound) {
		checkNotNull(leftClock);
		checkNotNull(rightClock);
		return new DiffGtConstrImpl(leftClock, rightClock, bound);
	}

	public static DiffGeqConstr Geq(final Clock leftClock, final Clock rightClock, final int bound) {
		checkNotNull(leftClock);
		checkNotNull(rightClock);
		return new DiffGeqConstrImpl(leftClock, rightClock, bound);
	}

	public static DiffEqConstr Eq(final Clock leftClock, final Clock rightClock, final int bound) {
		checkNotNull(leftClock);
		checkNotNull(rightClock);
		return new DiffEqConstrImpl(leftClock, rightClock, bound);
	}

	public static AndConstr And(final Collection<? extends Constr> constrs) {
		checkNotNull(constrs);
		return new AndConstrImpl(constrs);
	}

	////

	public static AndConstr And(final Constr... constrs) {
		checkNotNull(constrs);
		return And(ImmutableSet.copyOf(constrs));
	}

}
