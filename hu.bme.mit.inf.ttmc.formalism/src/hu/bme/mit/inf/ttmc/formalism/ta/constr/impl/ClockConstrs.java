package hu.bme.mit.inf.ttmc.formalism.ta.constr.impl;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;

import com.google.common.collect.ImmutableSet;

import hu.bme.mit.inf.ttmc.formalism.common.decl.ClockDecl;
import hu.bme.mit.inf.ttmc.formalism.ta.constr.AndConstr;
import hu.bme.mit.inf.ttmc.formalism.ta.constr.ClockConstr;
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

public final class ClockConstrs {

	private ClockConstrs() {
	}

	private static final TrueConstr TRUE_CONSTR;

	static {
		TRUE_CONSTR = new TrueConstrImpl();
	}

	public static TrueConstr True() {
		return TRUE_CONSTR;
	}

	public static UnitLtConstr Lt(final ClockDecl clock, final int bound) {
		checkNotNull(clock);
		return new UnitLtConstrImpl(clock, bound);
	}

	public static UnitLeqConstr Leq(final ClockDecl clock, final int bound) {
		checkNotNull(clock);
		return new UnitLeqConstrImpl(clock, bound);
	}

	public static UnitGtConstr Gt(final ClockDecl clock, final int bound) {
		checkNotNull(clock);
		return new UnitGtConstrImpl(clock, bound);
	}

	public static UnitGeqConstr Geq(final ClockDecl clock, final int bound) {
		checkNotNull(clock);
		return new UnitGeqConstrImpl(clock, bound);
	}

	public static UnitEqConstr Eq(final ClockDecl clock, final int bound) {
		checkNotNull(clock);
		return new UnitEqConstrImpl(clock, bound);
	}

	public static DiffLtConstr Lt(final ClockDecl leftClock, final ClockDecl rightClock, final int bound) {
		checkNotNull(leftClock);
		checkNotNull(rightClock);
		return new DiffLtConstrImpl(leftClock, rightClock, bound);
	}

	public static DiffLeqConstr Leq(final ClockDecl leftClock, final ClockDecl rightClock, final int bound) {
		checkNotNull(leftClock);
		checkNotNull(rightClock);
		return new DiffLeqConstrImpl(leftClock, rightClock, bound);
	}

	public static DiffGtConstr Gt(final ClockDecl leftClock, final ClockDecl rightClock, final int bound) {
		checkNotNull(leftClock);
		checkNotNull(rightClock);
		return new DiffGtConstrImpl(leftClock, rightClock, bound);
	}

	public static DiffGeqConstr Geq(final ClockDecl leftClock, final ClockDecl rightClock, final int bound) {
		checkNotNull(leftClock);
		checkNotNull(rightClock);
		return new DiffGeqConstrImpl(leftClock, rightClock, bound);
	}

	public static DiffEqConstr Eq(final ClockDecl leftClock, final ClockDecl rightClock, final int bound) {
		checkNotNull(leftClock);
		checkNotNull(rightClock);
		return new DiffEqConstrImpl(leftClock, rightClock, bound);
	}

	public static AndConstr And(final Collection<? extends ClockConstr> constrs) {
		checkNotNull(constrs);
		return new AndConstrImpl(constrs);
	}

	////

	public static AndConstr And(final ClockConstr... constrs) {
		checkNotNull(constrs);
		return And(ImmutableSet.copyOf(constrs));
	}

}
