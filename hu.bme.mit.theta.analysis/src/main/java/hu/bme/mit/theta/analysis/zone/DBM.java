package hu.bme.mit.theta.analysis.zone;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.theta.analysis.zone.DiffBounds.Inf;
import static hu.bme.mit.theta.analysis.zone.DiffBounds.Leq;
import static hu.bme.mit.theta.analysis.zone.DiffBounds.Lt;
import static hu.bme.mit.theta.analysis.zone.DiffBounds.asString;
import static hu.bme.mit.theta.analysis.zone.DiffBounds.negate;
import static java.lang.Math.max;
import static java.lang.Math.min;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;
import java.util.function.BiFunction;
import java.util.function.IntBinaryOperator;
import java.util.function.IntConsumer;
import java.util.stream.Collectors;

import com.google.common.collect.Sets;

import hu.bme.mit.theta.formalism.ta.constr.AndConstr;
import hu.bme.mit.theta.formalism.ta.constr.ClockConstr;
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
import hu.bme.mit.theta.formalism.ta.decl.ClockDecl;
import hu.bme.mit.theta.formalism.ta.op.ClockOp;
import hu.bme.mit.theta.formalism.ta.op.CopyOp;
import hu.bme.mit.theta.formalism.ta.op.FreeOp;
import hu.bme.mit.theta.formalism.ta.op.GuardOp;
import hu.bme.mit.theta.formalism.ta.op.ResetOp;
import hu.bme.mit.theta.formalism.ta.op.ShiftOp;
import hu.bme.mit.theta.formalism.ta.utils.ClockConstrVisitor;
import hu.bme.mit.theta.formalism.ta.utils.ClockOpVisitor;

final class DBM {

	private static final IntBinaryOperator ZERO_DBM_VALUES = (x, y) -> Leq(0);
	private static final IntBinaryOperator TOP_DBM_VALUES = SimpleDbm::defaultBound;
	private static final IntBinaryOperator BOTTOM_DBM_VALUES = (x, y) -> Leq(-1);

	private final DbmSignature signature;
	private final SimpleDbm dbm;

	private DBM(final DbmSignature signature, final IntBinaryOperator values) {
		this.signature = signature;
		this.dbm = new SimpleDbm(signature.size(), values);
	}

	private DBM(final DbmSignature signature, final SimpleDbm dbm) {
		checkNotNull(signature);
		checkNotNull(dbm);
		checkArgument(signature.size() == dbm.size());
		this.signature = signature;
		this.dbm = dbm;
	}

	// TODO replace BiFunction by IntBiFunction
	private DBM(final DbmSignature signature,
			final BiFunction<? super ClockDecl, ? super ClockDecl, ? extends Integer> values) {
		this(signature, (final int x, final int y) -> {
			return values.apply(signature.getClock(x), signature.getClock(y));
		});
	}

	private DBM(final DBM dbm) {
		this.signature = dbm.signature;
		this.dbm = new SimpleDbm(dbm.dbm);
	}

	////

	public Collection<DBM> complement() {
		final Collection<DBM> result = new ArrayList<>();
		if (!dbm.isConsistent()) {
			result.add(DBM.top(Collections.emptySet()));
		} else {
			for (final ClockDecl x : signature) {
				for (final ClockDecl y : signature) {
					final int bound = get(x, y);
					if (bound != defaultBound(x, y)) {
						final int newBound = negate(bound);
						final DbmSignature newSignature = DbmSignature.over(Arrays.asList(x, y));
						final BiFunction<ClockDecl, ClockDecl, Integer> newValues = (c1, c2) -> (c1 == y && c2 == x)
								? newBound : defaultBound(c1, c2);
						final DBM newDBM = new DBM(newSignature, newValues);
						result.add(newDBM);
					}
				}
			}
		}
		return result;
	}

	////

	public static DBM copyOf(final DBM dbm) {
		checkNotNull(dbm);
		return new DBM(dbm);
	}

	public static DBM zero(final Iterable<? extends ClockDecl> clocks) {
		checkNotNull(clocks);
		return new DBM(DbmSignature.over(clocks), ZERO_DBM_VALUES);
	}

	public static DBM top(final Iterable<? extends ClockDecl> clocks) {
		checkNotNull(clocks);
		return new DBM(DbmSignature.over(clocks), TOP_DBM_VALUES);
	}

	public static DBM bottom(final Iterable<? extends ClockDecl> clocks) {
		checkNotNull(clocks);
		return new DBM(DbmSignature.over(clocks), BOTTOM_DBM_VALUES);
	}

	public static DBM project(final DBM dbm, final Iterable<? extends ClockDecl> clocks) {
		checkNotNull(clocks);
		return new DBM(DbmSignature.over(clocks), dbm::getOrDefault);
	}

	////

	public static DBM intersection(final DBM dbm1, final DBM dbm2) {
		checkNotNull(dbm1);
		checkNotNull(dbm2);

		final DbmSignature signature = DbmSignature.union(dbm1.signature, dbm2.signature);
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

		final DbmSignature signature = DbmSignature.union(dbm1.signature, dbm2.signature);
		final BiFunction<ClockDecl, ClockDecl, Integer> values = (x, y) -> {
			final int bound1 = dbm1.getOrDefault(x, y);
			final int bound2 = dbm2.getOrDefault(x, y);
			return max(bound1, bound2);
		};

		final DBM result = new DBM(signature, values);
		return result;
	}

	////

	public static DBM interpolant2(final DBM dbmA, final DBM dbmB) {
		checkNotNull(dbmA);
		checkNotNull(dbmB);
		checkArgument(!dbmA.isConsistentWith(dbmB));

		if (!dbmA.isConsistent()) {
			return bottom(Collections.emptySet());
		}

		if (!dbmB.isConsistent()) {
			return top(Collections.emptySet());
		}

		final DbmSignature signature = interpolantSignature(dbmA, dbmB);
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

		assert dbmA.getRelation(result).isLeq();
		assert !dbmB.isConsistentWith(result);

		return result;
	}

	public static DBM interpolant(final DBM dbmA, final DBM dbmB) {
		checkNotNull(dbmA);
		checkNotNull(dbmB);

		if (!dbmA.isConsistent()) {
			return bottom(Collections.emptySet());
		}

		if (!dbmB.isConsistent()) {
			return top(Collections.emptySet());
		}

		final DbmSignature signature = interpolantSignature(dbmA, dbmB);
		final BiFunction<ClockDecl, ClockDecl, Integer> values = (x, y) -> {
			final int bound1 = dbmA.get(x, y);
			final int bound2 = dbmB.get(x, y);
			return min(bound1, bound2);
		};

		final DBM result = new DBM(signature, values);
		final int[] cycle = result.dbm.closeItp();
		result.free();

		for (int i = 0; i + 1 < cycle.length; i++) {
			final int x = cycle[i];
			final int y = cycle[i + 1];
			final ClockDecl leftClock = result.signature.getClock(x);
			final ClockDecl rightClock = result.signature.getClock(y);
			final int boundA = dbmA.get(leftClock, rightClock);
			final int boundB = dbmB.get(leftClock, rightClock);
			if (boundA < boundB) {
				result.dbm.set(x, y, boundA);
			}
		}

		assert result.isClosed();
		assert dbmA.getRelation(result).isLeq();
		assert !dbmB.isConsistentWith(result);

		return result;
	}

	private static DbmSignature interpolantSignature(final DBM dbmA, final DBM dbmB) {
		final Set<ClockDecl> clocksConstrainedByBothDBMS = Sets
				.intersection(dbmA.signature.toSet(), dbmB.signature.toSet()).stream()
				.filter(c -> dbmA.constrains(c) && dbmB.constrains(c)).collect(Collectors.toSet());
		return DbmSignature.over(clocksConstrainedByBothDBMS);
	}

	////

	private int getOrDefault(final ClockDecl x, final ClockDecl y) {
		if (!tracks(x) || !tracks(y)) {
			return defaultBound(x, y);
		} else {
			return get(x, y);
		}
	}

	@SuppressWarnings("unused")
	private void set(final ClockDecl x, final ClockDecl y, final int b) {
		checkArgument(tracks(x));
		checkArgument(tracks(y));
		final int i = signature.indexOf(x);
		final int j = signature.indexOf(y);
		dbm.set(i, j, b);
	}

	private int get(final ClockDecl x, final ClockDecl y) {
		checkArgument(tracks(x));
		checkArgument(tracks(y));
		final int i = signature.indexOf(x);
		final int j = signature.indexOf(y);
		return dbm.get(i, j);
	}

	private static int defaultBound(final ClockDecl x, final ClockDecl y) {
		if (x.equals(y)) {
			return Leq(0);
		} else {
			return Inf();
		}
	}

	////

	private boolean isClosed() {
		return dbm.isClosed();
	}

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

	public DbmRelation getRelation(final DBM that) {
		final Set<ClockDecl> clocks = Sets.union(this.signature.toSet(), that.signature.toSet());

		boolean leq = true;
		boolean geq = true;

		for (final ClockDecl x : clocks) {
			for (final ClockDecl y : clocks) {
				leq = leq && this.getOrDefault(x, y) <= that.getOrDefault(x, y);
				geq = geq && this.getOrDefault(x, y) >= that.getOrDefault(x, y);
			}
		}
		return DbmRelation.create(leq, geq);
	}

	public boolean isLeq(final DBM that) {
		final Set<ClockDecl> clocks = Sets.union(this.signature.toSet(), that.signature.toSet());

		for (final ClockDecl x : clocks) {
			for (final ClockDecl y : clocks) {
				if (this.getOrDefault(x, y) > that.getOrDefault(x, y)) {
					return false;
				}

			}
		}
		return true;
	}

	public Collection<ClockConstr> getConstrs() {
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

	public void execute(final ClockOp op) {
		checkNotNull(op);
		op.accept(ExecuteVisitor.INSTANCE, this);
	}

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
		ifTracks(clock, dbm::free);
	}

	public void free() {
		dbm.free();
	}

	public void reset(final ClockDecl clock, final int m) {
		checkNotNull(clock);
		checkArgument(!isZeroClock(clock));
		ifTracks(clock, x -> dbm.reset(x, m));
	}

	public void copy(final ClockDecl lhs, final ClockDecl rhs) {
		checkNotNull(lhs);
		checkNotNull(rhs);
		checkArgument(!isZeroClock(lhs));
		checkArgument(!isZeroClock(rhs));
		ifTracks(lhs, x -> ifTracksElse(rhs, y -> dbm.copy(x, y), () -> dbm.free(x)));
	}

	public void shift(final ClockDecl clock, final int m) {
		checkNotNull(clock);
		checkArgument(!isZeroClock(clock));
		ifTracks(clock, x -> dbm.shift(x, m));
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

	private void close() {
		dbm.close();
	}

	////

	@Override
	public int hashCode() {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

	@Override
	public boolean equals(final Object obj) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

	@Override
	public String toString() {
		final StringBuilder sb = new StringBuilder();

		sb.append(String.format("%-12s", ""));
		for (final ClockDecl clock : signature) {
			sb.append(String.format("%-12s", clock.getName()));
		}
		sb.append(System.lineSeparator());

		for (final ClockDecl x : signature) {
			sb.append(String.format("%-12s", x.getName()));
			for (final ClockDecl y : signature) {
				sb.append(String.format("%-12s", asString(get(x, y))));
			}
			sb.append(System.lineSeparator());
		}
		return sb.toString();
	}

	////

	private boolean tracks(final ClockDecl clock) {
		checkNotNull(clock);
		return signature.contains(clock);
	}

	private void ifTracks(final ClockDecl clock, final IntConsumer consumer) {
		if (tracks(clock)) {
			final int x = signature.indexOf(clock);
			consumer.accept(x);
		}
	}

	private void ifTracksElse(final ClockDecl clock, final IntConsumer consumer, final Procedure procedure) {
		if (tracks(clock)) {
			final int x = signature.indexOf(clock);
			consumer.accept(x);
		} else {
			procedure.execute();
		}
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
			dbm.dbm.and(0, 0, Lt(-1));
			return null;
		}

		@Override
		public Void visit(final UnitLtConstr constr, final DBM dbm) {
			final ClockDecl clock = constr.getClock();
			if (dbm.tracks(clock)) {
				final int x = dbm.signature.indexOf(clock);
				final int m = constr.getBound();
				dbm.dbm.and(x, 0, Lt(m));
			}
			return null;
		}

		@Override
		public Void visit(final UnitLeqConstr constr, final DBM dbm) {
			final ClockDecl clock = constr.getClock();
			if (dbm.tracks(clock)) {
				final int x = dbm.signature.indexOf(clock);
				final int m = constr.getBound();
				dbm.dbm.and(x, 0, Leq(m));
			}
			return null;
		}

		@Override
		public Void visit(final UnitGtConstr constr, final DBM dbm) {
			final ClockDecl clock = constr.getClock();
			if (dbm.tracks(clock)) {
				final int x = dbm.signature.indexOf(clock);
				final int m = constr.getBound();
				dbm.dbm.and(0, x, Lt(-m));
			}
			return null;
		}

		@Override
		public Void visit(final UnitGeqConstr constr, final DBM dbm) {
			final ClockDecl clock = constr.getClock();
			if (dbm.tracks(clock)) {
				final int x = dbm.signature.indexOf(clock);
				final int m = constr.getBound();
				dbm.dbm.and(0, x, Leq(-m));
			}
			return null;
		}

		@Override
		public Void visit(final UnitEqConstr constr, final DBM dbm) {
			final ClockDecl clock = constr.getClock();
			if (dbm.tracks(clock)) {
				final int x = dbm.signature.indexOf(clock);
				final int m = constr.getBound();
				dbm.dbm.and(x, 0, Leq(m));
				dbm.dbm.and(0, x, Leq(-m));
			}
			return null;
		}

		@Override
		public Void visit(final DiffLtConstr constr, final DBM dbm) {
			final ClockDecl leftClock = constr.getLeftClock();
			final ClockDecl rightClock = constr.getRightClock();
			if (dbm.tracks(leftClock) && dbm.tracks(rightClock)) {
				final int x = dbm.signature.indexOf(leftClock);
				final int y = dbm.signature.indexOf(rightClock);
				final int m = constr.getBound();
				dbm.dbm.and(x, y, Lt(m));
			}
			return null;
		}

		@Override
		public Void visit(final DiffLeqConstr constr, final DBM dbm) {
			final ClockDecl leftClock = constr.getLeftClock();
			final ClockDecl rightClock = constr.getRightClock();
			if (dbm.tracks(leftClock) && dbm.tracks(rightClock)) {
				final int x = dbm.signature.indexOf(leftClock);
				final int y = dbm.signature.indexOf(rightClock);
				final int m = constr.getBound();
				dbm.dbm.and(x, y, Leq(m));
			}
			return null;
		}

		@Override
		public Void visit(final DiffGtConstr constr, final DBM dbm) {
			final ClockDecl leftClock = constr.getLeftClock();
			final ClockDecl rightClock = constr.getRightClock();
			if (dbm.tracks(leftClock) && dbm.tracks(rightClock)) {
				final int x = dbm.signature.indexOf(leftClock);
				final int y = dbm.signature.indexOf(rightClock);
				final int m = constr.getBound();
				dbm.dbm.and(y, x, Lt(-m));
			}
			return null;
		}

		@Override
		public Void visit(final DiffGeqConstr constr, final DBM dbm) {
			final ClockDecl leftClock = constr.getLeftClock();
			final ClockDecl rightClock = constr.getRightClock();
			if (dbm.tracks(leftClock) && dbm.tracks(rightClock)) {
				final int x = dbm.signature.indexOf(leftClock);
				final int y = dbm.signature.indexOf(rightClock);
				final int m = constr.getBound();
				dbm.dbm.and(y, x, Leq(-m));
			}
			return null;
		}

		@Override
		public Void visit(final DiffEqConstr constr, final DBM dbm) {
			final ClockDecl leftClock = constr.getLeftClock();
			final ClockDecl rightClock = constr.getRightClock();
			if (dbm.tracks(leftClock) && dbm.tracks(rightClock)) {
				final int x = dbm.signature.indexOf(leftClock);
				final int y = dbm.signature.indexOf(rightClock);
				final int m = constr.getBound();
				dbm.dbm.and(x, y, Leq(m));
				dbm.dbm.and(y, x, Leq(-m));
			}
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

	@FunctionalInterface
	private interface Procedure {
		void execute();
	}
}
