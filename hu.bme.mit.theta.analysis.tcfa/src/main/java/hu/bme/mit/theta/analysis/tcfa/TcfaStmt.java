package hu.bme.mit.theta.analysis.tcfa;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.theta.core.stmt.Stmt;
import hu.bme.mit.theta.formalism.ta.op.ClockOp;
import hu.bme.mit.theta.formalism.ta.op.impl.ClockOps;

public abstract class TcfaStmt {
	private final Stmt stmt;

	private TcfaStmt(final Stmt stmt) {
		this.stmt = checkNotNull(stmt);
	}

	public static TcfaStmt of(final Stmt stmt) {
		if (TcfaUtils.isClockStmt(stmt)) {
			return new ClockStmt(stmt);
		} else if (TcfaUtils.isDataStmt(stmt)) {
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

	public static final class ClockStmt extends TcfaStmt {
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

	public static final class DataStmt extends TcfaStmt {

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
