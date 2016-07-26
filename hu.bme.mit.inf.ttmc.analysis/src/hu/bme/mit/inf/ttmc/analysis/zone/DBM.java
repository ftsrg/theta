package hu.bme.mit.inf.ttmc.analysis.zone;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.inf.ttmc.analysis.zone.DiffBounds.Inf;
import static hu.bme.mit.inf.ttmc.analysis.zone.DiffBounds.Leq;
import static hu.bme.mit.inf.ttmc.analysis.zone.DiffBounds.Lt;

import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;
import java.util.function.IntBinaryOperator;

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

	private final ExecuteVisitor executeVisitor;;
	private final AndOperationVisitor andVisitor;

	private final DBMSignature signature;
	private final SimpleDBM dbm;

	private DBM(final DBMSignature signature, final IntBinaryOperator values) {
		this.signature = signature;
		this.dbm = new SimpleDBM(signature.size(), values);
		executeVisitor = new ExecuteVisitor();
		andVisitor = new AndOperationVisitor();
	}

	private DBM(final DBM dbm) {
		this.signature = new DBMSignature(dbm.signature);
		this.dbm = new SimpleDBM(dbm.dbm);
		executeVisitor = new ExecuteVisitor();
		andVisitor = new AndOperationVisitor();

	}

	////

	public static DBM copyOf(final DBM dbm) {
		checkNotNull(dbm);
		return new DBM(dbm);
	}

	public static DBM zero(final Collection<? extends ClockDecl> clocks) {
		checkNotNull(clocks);
		return new DBM(new DBMSignature(clocks), ZERO_DBM_VALUES);
	}

	public static DBM top(final Collection<? extends ClockDecl> clocks) {
		checkNotNull(clocks);
		return new DBM(new DBMSignature(clocks), TOP_DBM_VALUES);
	}

	////

	public static DBM getInterpolant(final DBM dbmA, final DBM dbmB) {
		checkNotNull(dbmA);
		checkNotNull(dbmB);
		checkArgument(dbmA.getRelation(dbmB) == DBMRelation.DISJOINT);

		final Set<ClockDecl> clockDecls = Sets.intersection(dbmA.signature.asSet(), dbmB.signature.asSet());
		final DBM interpolant = DBM.top(clockDecls);

		for (final ClockDecl x : clockDecls) {
			for (final ClockDecl y : clockDecls) {
				if (dbmB.constrains(x) && dbmB.constrains(y)) {
					final int boundA = dbmA.getBound(x, y);
					final int boundB = dbmB.getBound(x, y);

					if (boundA < boundB) {
						interpolant.dbm.and(interpolant.signature.indexOf(x), interpolant.signature.indexOf(y), boundA);
					}
				}

			}
		}

		assert interpolant.isInterpolantFor(dbmA, dbmB);
		return interpolant;
	}

	private boolean isInterpolantFor(final DBM dbmA, final DBM dbmB) {
		if (this.getRelation(dbmA) != DBMRelation.GREATER) {
			return false;
		}

		if (this.getRelation(dbmB) != DBMRelation.DISJOINT) {
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

	private int getBound(final ClockDecl x, final ClockDecl y) {
		checkNotNull(x);
		checkNotNull(y);

		if (x.equals(y) || x.equals(ZeroClock.getInstance())) {
			return Leq(0);
		}

		if (!signature.isDefined(x) || !signature.isDefined(y)) {
			return Inf();
		}

		final int i = signature.indexOf(x);
		final int j = signature.indexOf(y);

		return dbm.get(i, j);
	}

	////

	public boolean isConsistent() {
		return dbm.isConsistent();
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
				leq = leq && this.getBound(x, y) <= that.getBound(x, y);
				geq = geq && this.getBound(x, y) >= that.getBound(x, y);
			}
		}
		return DBMRelation.create(leq, geq);
	}

	public Collection<ClockConstr> getConstraints() {
		final Collection<ClockConstr> result = new HashSet<>();

		for (final ClockDecl leftClock : signature) {
			for (final ClockDecl rightClock : signature) {
				final int b = getBound(leftClock, rightClock);
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
		op.accept(executeVisitor, null);
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
		constr.accept(andVisitor, null);
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

	public void norm(final Map<? super ClockDecl, ? extends Integer> bounds) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
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
		return dbm.toString();
	}

	////

	private boolean constrains(final ClockDecl clock) {
		checkNotNull(clock);
		return dbm.constrains(signature.indexOf(clock));
	}

	private boolean isZeroClock(final ClockDecl clock) {
		return clock.equals(ZeroClock.getInstance());
	}

	////

	private final class ExecuteVisitor implements ClockOpVisitor<Void, Void> {

		@Override
		public Void visit(final CopyOp op, final Void param) {
			copy(op.getClock(), op.getValue());
			return null;
		}

		@Override
		public Void visit(final FreeOp op, final Void param) {
			free(op.getClock());
			return null;
		}

		@Override
		public Void visit(final GuardOp op, final Void param) {
			and(op.getConstr());
			return null;
		}

		@Override
		public Void visit(final ResetOp op, final Void param) {
			reset(op.getClock(), op.getValue());
			return null;
		}

		@Override
		public Void visit(final ShiftOp op, final Void param) {
			shift(op.getClock(), op.getOffset());
			return null;
		}

	}

	////

	private final class AndOperationVisitor implements ClockConstrVisitor<Void, Void> {

		@Override
		public Void visit(final TrueConstr constr, final Void param) {
			return null;
		}

		@Override
		public Void visit(final FalseConstr constr, final Void param) {
			dbm.and(0, 0, -1);
			return null;
		}

		@Override
		public Void visit(final UnitLtConstr constr, final Void param) {
			final int x = signature.indexOf(constr.getClock());
			final int m = constr.getBound();
			dbm.and(x, 0, Lt(m));
			return null;
		}

		@Override
		public Void visit(final UnitLeqConstr constr, final Void param) {
			final int x = signature.indexOf(constr.getClock());
			final int m = constr.getBound();
			dbm.and(x, 0, Leq(m));
			return null;
		}

		@Override
		public Void visit(final UnitGtConstr constr, final Void param) {
			final int x = signature.indexOf(constr.getClock());
			final int m = constr.getBound();
			dbm.and(0, x, Lt(-m));
			return null;
		}

		@Override
		public Void visit(final UnitGeqConstr constr, final Void param) {
			final int x = signature.indexOf(constr.getClock());
			final int m = constr.getBound();
			dbm.and(0, x, Leq(-m));
			return null;
		}

		@Override
		public Void visit(final UnitEqConstr constr, final Void param) {
			final int x = signature.indexOf(constr.getClock());
			final int m = constr.getBound();
			dbm.and(x, 0, Leq(m));
			dbm.and(0, x, Leq(-m));
			return null;
		}

		@Override
		public Void visit(final DiffLtConstr constr, final Void param) {
			final int x = signature.indexOf(constr.getLeftClock());
			final int y = signature.indexOf(constr.getRightClock());
			final int m = constr.getBound();
			dbm.and(x, y, Lt(m));
			return null;
		}

		@Override
		public Void visit(final DiffLeqConstr constr, final Void param) {
			final int x = signature.indexOf(constr.getLeftClock());
			final int y = signature.indexOf(constr.getRightClock());
			final int m = constr.getBound();
			dbm.and(x, y, Leq(m));
			return null;
		}

		@Override
		public Void visit(final DiffGtConstr constr, final Void param) {
			final int x = signature.indexOf(constr.getLeftClock());
			final int y = signature.indexOf(constr.getRightClock());
			final int m = constr.getBound();
			dbm.and(y, x, Lt(-m));
			return null;
		}

		@Override
		public Void visit(final DiffGeqConstr constr, final Void param) {
			final int x = signature.indexOf(constr.getLeftClock());
			final int y = signature.indexOf(constr.getRightClock());
			final int m = constr.getBound();
			dbm.and(y, x, Leq(-m));
			return null;
		}

		@Override
		public Void visit(final DiffEqConstr constr, final Void param) {
			final int x = signature.indexOf(constr.getLeftClock());
			final int y = signature.indexOf(constr.getRightClock());
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
