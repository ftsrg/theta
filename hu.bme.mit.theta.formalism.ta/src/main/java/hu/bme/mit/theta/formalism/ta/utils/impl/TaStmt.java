package hu.bme.mit.theta.formalism.ta.utils.impl;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.theta.core.stmt.Stmt;
import hu.bme.mit.theta.formalism.ta.op.ClockOp;
import hu.bme.mit.theta.formalism.ta.op.ClockOps;

public abstract class TaStmt {
	private final Stmt stmt;

	private TaStmt(final Stmt stmt) {
		this.stmt = checkNotNull(stmt);
	}

	public static TaStmt of(final Stmt stmt) {
		if (TaUtils.isClockStmt(stmt)) {
			return new ClockStmt(stmt);
		} else if (TaUtils.isDataStmt(stmt)) {
			return new DataStmt(stmt);
		} else {
			throw new AssertionError();
		}
	}

	public final Stmt getStmt() {
		return stmt;
	}

	public abstract boolean isClockStmt();

	public abstract boolean isDataStmt();

	public abstract ClockStmt asClockStmt();

	public abstract DataStmt asDataStmt();

	////

	public static final class ClockStmt extends TaStmt {
		private final ClockOp clockOp;

		private ClockStmt(final Stmt stmt) {
			super(stmt);
			clockOp = ClockOps.fromStmt(stmt);
		}

		public ClockOp getClockOp() {
			return clockOp;
		}

		@Override
		public boolean isClockStmt() {
			return true;
		}

		@Override
		public boolean isDataStmt() {
			return false;
		}

		@Override
		public ClockStmt asClockStmt() {
			return this;
		}

		@Override
		public DataStmt asDataStmt() {
			throw new ClassCastException();
		}

	}

	public static final class DataStmt extends TaStmt {

		private DataStmt(final Stmt stmt) {
			super(stmt);
		}

		@Override
		public boolean isClockStmt() {
			return false;
		}

		@Override
		public boolean isDataStmt() {
			return true;
		}

		@Override
		public ClockStmt asClockStmt() {
			throw new ClassCastException();
		}

		@Override
		public DataStmt asDataStmt() {
			return this;
		}

	}

}
