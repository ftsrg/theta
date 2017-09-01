package hu.bme.mit.theta.formalism.xta;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.theta.core.clock.op.ClockOp;
import hu.bme.mit.theta.core.clock.op.ClockOps;
import hu.bme.mit.theta.core.stmt.Stmt;

public abstract class Update {

	private Update() {
	}

	static DataUpdate dataUpdate(final Stmt stmt) {
		return new DataUpdate(stmt);
	}

	static ClockUpdate clockUpdate(final Stmt stmt) {
		return new ClockUpdate(ClockOps.fromStmt(stmt));
	}

	public abstract Stmt toStmt();

	public abstract boolean isDataUpdate();

	public abstract boolean isClockUpdate();

	public abstract DataUpdate asDataUpdate();

	public abstract ClockUpdate asClockUpdate();

	public static final class DataUpdate extends Update {
		private final Stmt stmt;

		private DataUpdate(final Stmt stmt) {
			this.stmt = checkNotNull(stmt);
		}

		@Override
		public Stmt toStmt() {
			return stmt;
		}

		@Override
		public boolean isDataUpdate() {
			return true;
		}

		@Override
		public boolean isClockUpdate() {
			return false;
		}

		@Override
		public DataUpdate asDataUpdate() {
			return this;
		}

		@Override
		public ClockUpdate asClockUpdate() {
			throw new ClassCastException();
		}

	}

	public static final class ClockUpdate extends Update {
		private final ClockOp clockOp;

		private ClockUpdate(final ClockOp clockOp) {
			this.clockOp = checkNotNull(clockOp);
		}

		public ClockOp getClockOp() {
			return clockOp;
		}

		@Override
		public Stmt toStmt() {
			return clockOp.toStmt();
		}

		@Override
		public boolean isDataUpdate() {
			return false;
		}

		@Override
		public boolean isClockUpdate() {
			return true;
		}

		@Override
		public DataUpdate asDataUpdate() {
			throw new ClassCastException();
		}

		@Override
		public ClockUpdate asClockUpdate() {
			return this;
		}

	}

}
