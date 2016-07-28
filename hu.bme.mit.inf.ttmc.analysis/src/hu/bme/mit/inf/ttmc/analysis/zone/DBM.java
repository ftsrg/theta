package hu.bme.mit.inf.ttmc.analysis.zone;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.inf.ttmc.analysis.zone.DiffBounds.Inf;
import static hu.bme.mit.inf.ttmc.analysis.zone.DiffBounds.Leq;
import static hu.bme.mit.inf.ttmc.analysis.zone.DiffBounds.Lt;
import static java.lang.Math.max;
import static java.lang.Math.min;

import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;
import java.util.function.BiFunction;
import java.util.function.IntBinaryOperator;
import java.util.stream.Collectors;

import com.google.common.collect.Sets;

import hu.bme.mit.inf.ttmc.formalism.common.decl.ClockDecl;
import hu.bme.mit.inf.ttmc.formalism.ta.constr.AndConstr;
import hu.bme.mit.inf.ttmc.formalism.ta.constr.ClockConstr;
import hu.bme.mit.inf.ttmc.formalism.ta.constr.DiffEqConstr;
import hu.bme.mit.inf.ttmc.formalism.ta.constr.DiffGeqConstr;
import hu.bme.mit.inf.ttmc.formalism.ta.constr.DiffGtConstr;
import hu.bme.mit.inf.ttmc.formalism.ta.constr.DiffLeqConstr;
import hu.bme.mit.inf.ttmc.formalism.ta.constr.DiffLtConstr;
import hu.bme.mit.inf.ttmc.formalism.ta.constr.FalseConstr;
import hu.bme.mit.inf.ttmc.formalism.ta.constr.TrueConstr;
import hu.bme.mit.inf.ttmc.formalism.ta.constr.UnitEqConstr;
import hu.bme.mit.inf.ttmc.formalism.ta.constr.UnitGeqConstr;
import hu.bme.mit.inf.ttmc.formalism.ta.constr.UnitGtConstr;
import hu.bme.mit.inf.ttmc.formalism.ta.constr.UnitLeqConstr;
import hu.bme.mit.inf.ttmc.formalism.ta.constr.UnitLtConstr;
import hu.bme.mit.inf.ttmc.formalism.ta.op.ClockOp;
import hu.bme.mit.inf.ttmc.formalism.ta.op.CopyOp;
import hu.bme.mit.inf.ttmc.formalism.ta.op.FreeOp;
import hu.bme.mit.inf.ttmc.formalism.ta.op.GuardOp;
import hu.bme.mit.inf.ttmc.formalism.ta.op.ResetOp;
import hu.bme.mit.inf.ttmc.formalism.ta.op.ShiftOp;
import hu.bme.mit.inf.ttmc.formalism.ta.utils.ClockConstrVisitor;
import hu.bme.mit.inf.ttmc.formalism.ta.utils.ClockOpVisitor;

final class DBM {

	private static final IntBinaryOperator ZERO_DBM_VALUES = (x, y) -> Leq(0);
	private static final IntBinaryOperator TOP_DBM_VALUES = SimpleDBM::defaultBound;

	private final DBMSignature signature;
	private final SimpleDBM dbm;

	private DBM(final DBMSignature signature, final IntBinaryOperator values) {
		this.signature = signature;
		this.dbm = new SimpleDBM(signature.size(), values);
	}

	private DBM(final DBMSignature signature, final BiFunction<ClockDecl, ClockDecl, Integer> values) {
		this(signature, (final int x, final int y) -> {
			return values.apply(signature.getClock(x), signature.getClock(y));
		});
	}

	private DBM(final DBM dbm) {
		this.signature = DBMSignature.copyOf(dbm.signature);
		this.dbm = new SimpleDBM(dbm.dbm);
	}

	////

	public static DBM copyOf(final DBM dbm) {
		checkNotNull(dbm);
		return new DBM(dbm);
	}

	public static DBM zero(final Collection<? extends ClockDecl> clocks) {
		checkNotNull(clocks);
		return new DBM(DBMSignature.over(clocks), ZERO_DBM_VALUES);
	}

	public static DBM top(final Collection<? extends ClockDecl> clocks) {
		checkNotNull(clocks);
		return new DBM(DBMSignature.over(clocks), TOP_DBM_VALUES);
	}

	////

	public static DBM intersection(final DBM dbm1, final DBM dbm2) {
		checkNotNull(dbm1);
		checkNotNull(dbm2);

		final DBMSignature signature = DBMSignature.union(dbm1.signature, dbm2.signature);
		final BiFunction<ClockDecl, ClockDecl, Integer> values = (x, y) -> {
			final int bound1 = dbm1.getOrDefault(x, y);
			final int bound2 = dbm2.getOrDefault(x, y);
			return min(bound1, bound2);
		};

		final DBM result = new DBM(signature, values);
		result.close();

		return result;
	}

	public static DBM enclosure(final DBM dbm1, final DBM dbm2) {
		checkNotNull(dbm1);
		checkNotNull(dbm2);

		final DBMSignature signature = DBMSignature.union(dbm1.signature, dbm2.signature);
		final BiFunction<ClockDecl, ClockDecl, Integer> values = (x, y) -> {
			final int bound1 = dbm1.getOrDefault(x, y);
			final int bound2 = dbm2.getOrDefault(x, y);
			return max(bound1, bound2);
		};

		final DBM result = new DBM(signature, values);
		return result;
	}

	////

	public static DBM interpolant(final DBM dbmA, final DBM dbmB) {
		checkNotNull(dbmA);
		checkNotNull(dbmB);
		checkArgument(!dbmA.isConsistentWith(dbmB));

		final DBMSignature signature = interpolantSignature(dbmA, dbmB);
		final BiFunction<ClockDecl, ClockDecl, Integer> values = (x, y) -> {
			final int boundA = dbmA.get(x, y);
			final int boundB = dbmB.get(x, y);
			if (boundA < boundB) {
				return boundA;
			} else {
				return defaultBound(x, y);
			}
		};

		final DBM result = new DBM(signature, values);
		result.close();

		assert result.isInterpolant(dbmA, dbmB);
		return result;
	}

	private static DBMSignature interpolantSignature(final DBM dbmA, final DBM dbmB) {
		final Set<ClockDecl> clocksConstrainedByBothDBMS = Sets
				.intersection(dbmA.signature.asSet(), dbmB.signature.asSet()).stream()
				.filter(c -> dbmA.constrains(c) && dbmB.constrains(c)).collect(Collectors.toSet());
		return DBMSignature.over(clocksConstrainedByBothDBMS);
	}

	private boolean isInterpolant(final DBM dbmA, final DBM dbmB) {
		if (this.getRelation(dbmA) != DBMRelation.GREATER) {
			return false;
		}

		if (this.isConsistentWith(dbmB)) {
			return false;
		}

		for (final ClockDecl clock : signature) {
			if (this.constrains(clock)) {
				if (!dbmA.constrains(clock)) {
					return false;
				}

				if (!dbmB.constrains(clock)) {
					return false;
				}
			}
		}

		return true;
	}

	////

	private int getOrDefault(final ClockDecl x, final ClockDecl y) {
		checkNotNull(x);
		checkNotNull(y);
		if (!tracks(x) || !tracks(y)) {
			return defaultBound(x, y);
		} else {
			return get(x, y);
		}
	}

	private int get(final ClockDecl x, final ClockDecl y) {
		checkNotNull(x);
		checkNotNull(y);
		checkArgument(tracks(x));
		checkArgument(tracks(y));
		final int i = signature.indexOf(x);
		final int j = signature.indexOf(y);
		return dbm.get(i, j);
	}

	private static int defaultBound(final ClockDecl x, final ClockDecl y) {
		checkNotNull(x);
		checkNotNull(y);
		if (x.equals(y) || x.equals(ZeroClock.getInstance())) {
			return Leq(0);
		} else {
			return Inf();
		}
	}

	////

	public boolean isConsistent() {
		return dbm.isConsistent();
	}

	public boolean isConsistentWith(final DBM dbm) {
		checkNotNull(dbm);
		return intersection(this, dbm).isConsistent();
	}

	public boolean isSatisfied(final ClockConstr constr) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

	public DBMRelation getRelation(final DBM that) {
		final Set<ClockDecl> clocks = Sets.union(this.signature.asSet(), that.signature.asSet());

		boolean leq = true;
		boolean geq = true;

		for (final ClockDecl x : clocks) {
			for (final ClockDecl y : clocks) {
				leq = leq && this.getOrDefault(x, y) <= that.getOrDefault(x, y);
				geq = geq && this.getOrDefault(x, y) >= that.getOrDefault(x, y);
			}
		}
		return DBMRelation.create(leq, geq);
	}

	public Collection<ClockConstr> getConstraints() {
		final Collection<ClockConstr> result = new HashSet<>();

		for (final ClockDecl leftClock : signature) {
			for (final ClockDecl rightClock : signature) {
				final int b = get(leftClock, rightClock);
				final ClockConstr constr = DiffBounds.toConstr(leftClock, rightClock, b);

				if (constr instanceof TrueConstr) {
					continue;
				} else if (constr instanceof FalseConstr) {
					return Collections.singleton(constr);
				} else {
					result.add(constr);
				}
			}
		}

		return result;
	}

	////

	public void track(final ClockDecl clock) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

	public void untrack(final ClockDecl clock) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

	public void execute(final ClockOp op) {
		checkNotNull(op);
		op.accept(ExecuteVisitor.INSTANCE, this);
	}

	////

	public void up() {
		dbm.up();
	}

	public void down() {
		dbm.down();
	}

	public void and(final ClockConstr constr) {
		checkNotNull(constr);
		constr.accept(AndOperationVisitor.INSTANCE, this);
	}

	public void free(final ClockDecl clock) {
		checkNotNull(clock);
		checkArgument(!isZeroClock(clock));
		final int x = signature.indexOf(clock);
		dbm.free(x);

	}

	public void reset(final ClockDecl clock, final int m) {
		checkNotNull(clock);
		checkArgument(!isZeroClock(clock));
		final int x = signature.indexOf(clock);
		dbm.reset(x, m);
	}

	public void copy(final ClockDecl lhs, final ClockDecl rhs) {
		checkNotNull(lhs);
		checkNotNull(rhs);
		checkArgument(!isZeroClock(lhs));
		checkArgument(!isZeroClock(rhs));
		final int x = signature.indexOf(lhs);
		final int y = signature.indexOf(rhs);
		dbm.copy(x, y);
	}

	public void shift(final ClockDecl clock, final int m) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

	public void norm(final Map<? extends ClockDecl, ? extends Integer> bounds) {
		final int[] k = new int[signature.size()];
		for (int i = 0; i < signature.size(); i++) {
			final ClockDecl clock = signature.getClock(i);
			final Integer bound = bounds.get(clock);
			if (bound != null) {
				k[i] = bound;
			} else {
				k[i] = DiffBounds.getBound(Inf());
			}
		}
		dbm.norm(k);
	}

	////

	private void close() {
		dbm.close();
	}

	////

	@Override
	public String toString() {
		return dbm.toString();
	}

	////

	private boolean tracks(final ClockDecl clock) {
		checkNotNull(clock);
		return signature.contains(clock);
	}

	private boolean constrains(final ClockDecl clock) {
		checkNotNull(clock);
		return this.tracks(clock) && dbm.constrains(signature.indexOf(clock));
	}

	private boolean isZeroClock(final ClockDecl clock) {
		return clock.equals(ZeroClock.getInstance());
	}

	////

	private static final class ExecuteVisitor implements ClockOpVisitor<DBM, Void> {

		private static final ExecuteVisitor INSTANCE = new ExecuteVisitor();

		private ExecuteVisitor() {
		}

		@Override
		public Void visit(final CopyOp op, final DBM dbm) {
			dbm.copy(op.getClock(), op.getValue());
			return null;
		}

		@Override
		public Void visit(final FreeOp op, final DBM dbm) {
			dbm.free(op.getClock());
			return null;
		}

		@Override
		public Void visit(final GuardOp op, final DBM dbm) {
			dbm.and(op.getConstr());
			return null;
		}

		@Override
		public Void visit(final ResetOp op, final DBM dbm) {
			dbm.reset(op.getClock(), op.getValue());
			return null;
		}

		@Override
		public Void visit(final ShiftOp op, final DBM dbm) {
			dbm.shift(op.getClock(), op.getOffset());
			return null;
		}

	}

	////

	private static final class AndOperationVisitor implements ClockConstrVisitor<DBM, Void> {

		private static final AndOperationVisitor INSTANCE = new AndOperationVisitor();

		private AndOperationVisitor() {
		}

		@Override
		public Void visit(final TrueConstr constr, final DBM dbm) {
			return null;
		}

		@Override
		public Void visit(final FalseConstr constr, final DBM dbm) {
			dbm.dbm.and(0, 0, -1);
			return null;
		}

		@Override
		public Void visit(final UnitLtConstr constr, final DBM dbm) {
			final int x = dbm.signature.indexOf(constr.getClock());
			final int m = constr.getBound();
			dbm.dbm.and(x, 0, Lt(m));
			return null;
		}

		@Override
		public Void visit(final UnitLeqConstr constr, final DBM dbm) {
			final int x = dbm.signature.indexOf(constr.getClock());
			final int m = constr.getBound();
			dbm.dbm.and(x, 0, Leq(m));
			return null;
		}

		@Override
		public Void visit(final UnitGtConstr constr, final DBM dbm) {
			final int x = dbm.signature.indexOf(constr.getClock());
			final int m = constr.getBound();
			dbm.dbm.and(0, x, Lt(-m));
			return null;
		}

		@Override
		public Void visit(final UnitGeqConstr constr, final DBM dbm) {
			final int x = dbm.signature.indexOf(constr.getClock());
			final int m = constr.getBound();
			dbm.dbm.and(0, x, Leq(-m));
			return null;
		}

		@Override
		public Void visit(final UnitEqConstr constr, final DBM dbm) {
			final int x = dbm.signature.indexOf(constr.getClock());
			final int m = constr.getBound();
			dbm.dbm.and(x, 0, Leq(m));
			dbm.dbm.and(0, x, Leq(-m));
			return null;
		}

		@Override
		public Void visit(final DiffLtConstr constr, final DBM dbm) {
			final int x = dbm.signature.indexOf(constr.getLeftClock());
			final int y = dbm.signature.indexOf(constr.getRightClock());
			final int m = constr.getBound();
			dbm.dbm.and(x, y, Lt(m));
			return null;
		}

		@Override
		public Void visit(final DiffLeqConstr constr, final DBM dbm) {
			final int x = dbm.signature.indexOf(constr.getLeftClock());
			final int y = dbm.signature.indexOf(constr.getRightClock());
			final int m = constr.getBound();
			dbm.dbm.and(x, y, Leq(m));
			return null;
		}

		@Override
		public Void visit(final DiffGtConstr constr, final DBM dbm) {
			final int x = dbm.signature.indexOf(constr.getLeftClock());
			final int y = dbm.signature.indexOf(constr.getRightClock());
			final int m = constr.getBound();
			dbm.dbm.and(y, x, Lt(-m));
			return null;
		}

		@Override
		public Void visit(final DiffGeqConstr constr, final DBM dbm) {
			final int x = dbm.signature.indexOf(constr.getLeftClock());
			final int y = dbm.signature.indexOf(constr.getRightClock());
			final int m = constr.getBound();
			dbm.dbm.and(y, x, Leq(-m));
			return null;
		}

		@Override
		public Void visit(final DiffEqConstr constr, final DBM dbm) {
			final int x = dbm.signature.indexOf(constr.getLeftClock());
			final int y = dbm.signature.indexOf(constr.getRightClock());
			final int m = constr.getBound();
			dbm.dbm.and(x, y, Leq(m));
			dbm.dbm.and(y, x, Leq(-m));
			return null;
		}

		@Override
		public Void visit(final AndConstr constr, final DBM dbm) {
			for (final ClockConstr atomicConstr : constr.getConstrs()) {
				atomicConstr.accept(this, dbm);
				if (!dbm.dbm.isConsistent()) {
					return null;
				}
			}
			return null;
		}
	}

}
