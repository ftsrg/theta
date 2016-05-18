package hu.bme.mit.inf.ttmc.analysis.zone;

import static hu.bme.mit.inf.ttmc.analysis.zone.DiffBounds.Leq;
import static hu.bme.mit.inf.ttmc.analysis.zone.DiffBounds.Lt;

import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Set;
import java.util.function.Consumer;

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

final class DBMWithSignature {

	private static final int HASH_SEED = 7211;

	private volatile int hashCode = 0;

	private final Map<ClockDecl, Integer> clockToIndex;
	private final DBM dbm;

	private final AndOperationVisitor visitor;

	private DBMWithSignature(final Map<ClockDecl, Integer> clockToIndex, final DBM dbm) {
		this.clockToIndex = clockToIndex;
		this.dbm = dbm;
		visitor = new AndOperationVisitor();
	}

	////////

	public static DBMWithSignature zero(final Set<? extends ClockDecl> clockDecls) {
		final Map<ClockDecl, Integer> clockToIndex = toIndexMap(clockDecls);
		return new DBMWithSignature(clockToIndex, DBM.zero(clockDecls.size()));
	}

	public static DBMWithSignature nonNegative(final Set<? extends ClockDecl> clockDecls) {
		final Map<ClockDecl, Integer> clockToIndex = toIndexMap(clockDecls);
		return new DBMWithSignature(clockToIndex, DBM.nonNegative(clockDecls.size()));
	}

	public static DBMWithSignature top(final Set<? extends ClockDecl> clockDecls) {
		final Map<ClockDecl, Integer> clockToIndex = toIndexMap(clockDecls);
		return new DBMWithSignature(clockToIndex, DBM.top(clockDecls.size()));
	}

	public static DBMWithSignature bottom() {
		final Map<ClockDecl, Integer> clockToIndex = Collections.emptyMap();
		return new DBMWithSignature(clockToIndex, DBM.bottom());
	}

	public static DBMWithSignature copyOf(final DBMWithSignature other) {
		final Map<ClockDecl, Integer> clockToIndex = new LinkedHashMap<>(other.clockToIndex);
		final DBM dbm = DBM.copyOf(other.dbm);
		return new DBMWithSignature(clockToIndex, dbm);
	}

	////////

	public void up() {
		dbm.up();
	}

	public void down() {
		dbm.down();
	}

	public void and(final ClockConstr constr) {
		constr.accept(visitor, null);
	}

	public void free(final ClockDecl clock) {
		doIfDeclared(clock, dbm::free);
	}

	public void reset(final ClockDecl clock, final int m) {
		final int index = declareAndGetIndex(clock);
		dbm.reset(index, m);
	}

	public void copy(final ClockDecl lhs, final ClockDecl rhs) {
		final Integer rhsIndex = getIndex(rhs);
		if (rhsIndex != null) {
			final int lhsIndex = declareAndGetIndex(lhs);
			dbm.copy(lhsIndex, rhsIndex);
		} else {
			doIfDeclared(lhs, dbm::free);
		}
	}

	public void shift(final ClockDecl clock, final int m) {
		doIfDeclared(clock, i -> dbm.shift(i, m));
	}

	////////

	@Override
	public int hashCode() {
		int result = hashCode;
		if (result == 0) {
			result = HASH_SEED;
			result = 31 * result + dbm.hashCode();
			hashCode = result;
		}
		return result;
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		} else if (obj instanceof DBMWithSignature) {
			final DBMWithSignature that = (DBMWithSignature) obj;
			return this.dbm.equals(that.dbm);
		} else {
			return false;
		}
	}

	@Override
	public String toString() {
		final StringBuilder sb = new StringBuilder();
		sb.append(String.format("%-12s", ""));
		for (final ClockDecl clockDecl : clockToIndex.keySet()) {
			sb.append(String.format("%-12s", clockDecl.getName()));
		}
		sb.append(System.lineSeparator());
		sb.append(dbm);
		return sb.toString();
	}

	////////

	private static Map<ClockDecl, Integer> toIndexMap(final Set<? extends ClockDecl> clockDecls) {
		final Map<ClockDecl, Integer> result = new LinkedHashMap<ClockDecl, Integer>();
		int i = 1;
		for (final ClockDecl clockDecl : clockDecls) {
			result.put(clockDecl, i);
			i++;
		}
		return result;
	}

	private Integer getIndex(final ClockDecl clock) {
		return clockToIndex.get(clock);
	}

	private void doIfDeclared(final ClockDecl clock, final Consumer<? super Integer> operation) {
		final Integer index = getIndex(clock);
		if (index != null) {
			operation.accept(index);
		}
	}

	private int declareAndGetIndex(final ClockDecl clock) {
		Integer index = getIndex(clock);
		if (index == null) {
			dbm.expand();
			index = dbm.nClocks();
			clockToIndex.put(clock, index);
		}
		return index;
	}

	////////

	private class AndOperationVisitor implements ClockConstrVisitor<Void, Void> {

		@Override
		public Void visit(final TrueConstr constr, final Void param) {
			return null;
		}

		@Override
		public Void visit(final UnitLtConstr constr, final Void param) {
			final int x = declareAndGetIndex(constr.getClock());
			final int m = constr.getBound();
			dbm.and(x, 0, Lt(m));
			return null;
		}

		@Override
		public Void visit(final UnitLeqConstr constr, final Void param) {
			final int x = declareAndGetIndex(constr.getClock());
			final int m = constr.getBound();
			dbm.and(x, 0, Leq(m));
			return null;
		}

		@Override
		public Void visit(final UnitGtConstr constr, final Void param) {
			final int x = declareAndGetIndex(constr.getClock());
			final int m = constr.getBound();
			dbm.and(0, x, Lt(-m));
			return null;
		}

		@Override
		public Void visit(final UnitGeqConstr constr, final Void param) {
			final int x = declareAndGetIndex(constr.getClock());
			final int m = constr.getBound();
			dbm.and(0, x, Leq(-m));
			return null;
		}

		@Override
		public Void visit(final UnitEqConstr constr, final Void param) {
			final int x = declareAndGetIndex(constr.getClock());
			final int m = constr.getBound();
			dbm.and(x, 0, Leq(m));
			dbm.and(0, x, Leq(-m));
			return null;
		}

		@Override
		public Void visit(final DiffLtConstr constr, final Void param) {
			final int x = declareAndGetIndex(constr.getLeftClock());
			final int y = declareAndGetIndex(constr.getRightClock());
			final int m = constr.getBound();
			dbm.and(x, y, Lt(m));
			return null;
		}

		@Override
		public Void visit(final DiffLeqConstr constr, final Void param) {
			final int x = declareAndGetIndex(constr.getLeftClock());
			final int y = declareAndGetIndex(constr.getRightClock());
			final int m = constr.getBound();
			dbm.and(x, y, Leq(m));
			return null;
		}

		@Override
		public Void visit(final DiffGtConstr constr, final Void param) {
			final int x = declareAndGetIndex(constr.getLeftClock());
			final int y = declareAndGetIndex(constr.getRightClock());
			final int m = constr.getBound();
			dbm.and(y, x, Lt(-m));
			return null;
		}

		@Override
		public Void visit(final DiffGeqConstr constr, final Void param) {
			final int x = declareAndGetIndex(constr.getLeftClock());
			final int y = declareAndGetIndex(constr.getRightClock());
			final int m = constr.getBound();
			dbm.and(y, x, Leq(-m));
			return null;
		}

		@Override
		public Void visit(final DiffEqConstr constr, final Void param) {
			final int x = declareAndGetIndex(constr.getLeftClock());
			final int y = declareAndGetIndex(constr.getRightClock());
			final int m = constr.getBound();
			dbm.and(x, y, Leq(m));
			dbm.and(y, x, Leq(-m));
			return null;
		}

		@Override
		public Void visit(final AndConstr constr, final Void param) {
			for (final ClockConstr atomicConstr : constr.getConstrs()) {
				atomicConstr.accept(this, param);
				if (!dbm.isConsistent()) {
					return null;
				}
			}
			return null;
		}

	}

}
