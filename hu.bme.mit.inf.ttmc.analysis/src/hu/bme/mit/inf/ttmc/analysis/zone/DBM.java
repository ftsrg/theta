package hu.bme.mit.inf.ttmc.analysis.zone;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.inf.ttmc.analysis.zone.DiffBounds.Inf;
import static hu.bme.mit.inf.ttmc.analysis.zone.DiffBounds.Leq;
import static hu.bme.mit.inf.ttmc.analysis.zone.DiffBounds.Lt;
import static hu.bme.mit.inf.ttmc.analysis.zone.DiffBounds.add;
import static hu.bme.mit.inf.ttmc.analysis.zone.DiffBounds.asString;
import static hu.bme.mit.inf.ttmc.formalism.common.decl.impl.Decls2.Clock;

import java.util.Collection;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.Set;

import com.google.common.collect.Sets;

import hu.bme.mit.inf.ttmc.common.matrix.IntMatrix;
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
import hu.bme.mit.inf.ttmc.formalism.ta.utils.ClockConstrVisitor;

public final class DBM {

	static final ClockDecl ZERO_CLOCK;

	private final LinkedHashMap<ClockDecl, Integer> clockToIndex;

	private final int nClocks;
	private final IntMatrix matrix;

	private final ZoneConsistencyVisitor visitor;

	static {
		ZERO_CLOCK = Clock("_zero");
	}

	DBM(final DBMBuilder builder) {
		clockToIndex = builder.clockToIndex;
		nClocks = builder.nClocks;
		matrix = builder.matrix;
		visitor = new ZoneConsistencyVisitor();
	}

	////

	public static DBM top(final Collection<? extends ClockDecl> clocks) {
		final DBM result = builder(clocks).build();
		return result;
	}

	public static DBM zero(final Collection<? extends ClockDecl> clocks) {
		checkArgument(!clocks.contains(ZERO_CLOCK));
		final DBM result = builder(clocks).build();
		result.matrix.fill(Leq(0));
		return result;
	}

	////

	public static DBMBuilder builder() {
		return builder(Collections.emptySet());
	}

	public static DBMBuilder builder(final Collection<? extends ClockDecl> clocks) {
		return new DBMBuilder(clocks);
	}

	public DBMBuilder transform() {
		return new DBMBuilder(clockToIndex, matrix);
	}

	////

	public Collection<ClockDecl> getClocks() {
		return Collections.unmodifiableCollection(clockToIndex.keySet());
	}

	////

	public boolean isTracked(final ClockDecl clock) {
		return clockToIndex.containsKey(clock);
	}

	public boolean isConsistent() {
		return matrix.get(0, 0) >= 0;
	}

	public boolean isConsistent(final ClockConstr constr) {
		return constr.accept(visitor, null);
	}

	////

	public DBMRelation getRelation(final DBM that) {
		final Set<ClockDecl> clockDecls = Sets.union(this.clockToIndex.keySet(), that.clockToIndex.keySet());

		boolean leq = true;
		boolean geq = true;

		for (final ClockDecl x : clockDecls) {
			for (final ClockDecl y : clockDecls) {
				leq = leq && this.getBound(x, y) <= that.getBound(x, y);
				geq = geq && this.getBound(x, y) >= that.getBound(x, y);
			}
		}
		return DBMRelation.create(leq, geq);
	}

	////

	@Override
	public int hashCode() {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		} else if (obj instanceof DBM) {
			final DBM that = (DBM) obj;
			return this.getRelation(that).equals(DBMRelation.EQUAL);
		} else {
			return false;
		}
	}

	@Override
	public String toString() {
		final StringBuilder sb = new StringBuilder();

		for (final ClockDecl clockDecl : clockToIndex.keySet()) {
			sb.append(String.format("%-12s", clockDecl.getName()));
		}

		sb.append(System.lineSeparator());

		for (int i = 0; i <= nClocks; i++) {
			for (int j = 0; j <= nClocks; j++) {
				sb.append(String.format("%-12s", asString(matrix.get(i, j))));
			}
			sb.append(System.lineSeparator());
		}
		return sb.toString();
	}

	////

	private int getBound(final ClockDecl x, final ClockDecl y) {
		checkNotNull(x);
		checkNotNull(y);

		if (x.equals(y) || x.equals(ZERO_CLOCK)) {
			return Leq(0);
		}

		final Integer i = clockToIndex.get(x);
		final Integer j = clockToIndex.get(y);

		if (i == null || j == null) {
			return Inf();
		}

		return matrix.get(i, j);
	}

	////

	private final class ZoneConsistencyVisitor implements ClockConstrVisitor<Void, Boolean> {

		private boolean isConsistent(final int x, final int y, final int b) {
			return add(matrix.get(y, x), b) >= 0;
		}

		@Override
		public Boolean visit(final TrueConstr constr, final Void param) {
			return true;
		}

		@Override
		public Boolean visit(final UnitLtConstr constr, final Void param) {
			final Integer x = clockToIndex.get(constr.getClock());
			if (x == null) {
				return constr.getBound() > 0;
			} else {
				return isConsistent(x, 0, Lt(constr.getBound()));
			}
		}

		@Override
		public Boolean visit(final UnitLeqConstr constr, final Void param) {
			final Integer x = clockToIndex.get(constr.getClock());
			if (x == null) {
				return constr.getBound() >= 0;
			} else {
				return isConsistent(x, 0, Leq(constr.getBound()));
			}
		}

		@Override
		public Boolean visit(final UnitGtConstr constr, final Void param) {
			final Integer x = clockToIndex.get(constr.getClock());
			if (x == null) {
				return true;
			} else {
				return isConsistent(0, x, Lt(-constr.getBound()));
			}
		}

		@Override
		public Boolean visit(final UnitGeqConstr constr, final Void param) {
			final Integer x = clockToIndex.get(constr.getClock());
			if (x == null) {
				return true;
			} else {
				return isConsistent(0, x, Leq(-constr.getBound()));
			}
		}

		@Override
		public Boolean visit(final UnitEqConstr constr, final Void param) {
			final Integer x = clockToIndex.get(constr.getClock());
			if (x == null) {
				return constr.getBound() >= 0;
			} else {
				return isConsistent(x, 0, Leq(constr.getBound())) && isConsistent(0, x, Leq(-constr.getBound()));
			}
		}

		@Override
		public Boolean visit(final DiffLtConstr constr, final Void param) {
			if (constr.getLeftClock().equals(constr.getRightClock())) {
				return constr.getBound() > 0;
			}

			final Integer x = clockToIndex.get(constr.getLeftClock());
			final Integer y = clockToIndex.get(constr.getRightClock());

			if (x == null || y == null) {
				return true;
			} else {
				return isConsistent(x, y, Lt(constr.getBound()));
			}
		}

		@Override
		public Boolean visit(final DiffLeqConstr constr, final Void param) {
			if (constr.getLeftClock().equals(constr.getRightClock())) {
				return constr.getBound() >= 0;
			}

			final Integer x = clockToIndex.get(constr.getLeftClock());
			final Integer y = clockToIndex.get(constr.getRightClock());

			if (x == null || y == null) {
				return true;
			} else {
				return isConsistent(x, y, Leq(constr.getBound()));
			}
		}

		@Override
		public Boolean visit(final DiffGtConstr constr, final Void param) {
			if (constr.getLeftClock().equals(constr.getRightClock())) {
				return constr.getBound() < 0;
			}

			final Integer x = clockToIndex.get(constr.getLeftClock());
			final Integer y = clockToIndex.get(constr.getRightClock());

			if (x == null || y == null) {
				return true;
			} else {
				return isConsistent(y, x, Lt(-constr.getBound()));
			}
		}

		@Override
		public Boolean visit(final DiffGeqConstr constr, final Void param) {
			if (constr.getLeftClock().equals(constr.getRightClock())) {
				return constr.getBound() <= 0;
			}

			final Integer x = clockToIndex.get(constr.getLeftClock());
			final Integer y = clockToIndex.get(constr.getRightClock());

			if (x == null || y == null) {
				return true;
			} else {
				return isConsistent(y, x, Leq(-constr.getBound()));
			}
		}

		@Override
		public Boolean visit(final DiffEqConstr constr, final Void param) {
			if (constr.getLeftClock().equals(constr.getRightClock())) {
				return constr.getBound() == 0;
			}

			final Integer x = clockToIndex.get(constr.getLeftClock());
			final Integer y = clockToIndex.get(constr.getRightClock());

			if (x == null || y == null) {
				return true;
			} else {
				return isConsistent(x, y, Leq(constr.getBound())) && isConsistent(y, x, Leq(-constr.getBound()));
			}
		}

		@Override
		public Boolean visit(final AndConstr constr, final Void param) {
			return constr.getConstrs().stream().allMatch(c -> c.accept(this, null));
		}
	}

}
