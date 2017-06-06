package hu.bme.mit.theta.formalism.xta;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.theta.core.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.formalism.ta.constr.ClockConstr;
import hu.bme.mit.theta.formalism.ta.constr.ClockConstrs;

public abstract class Guard {

	private Guard() {
	}

	static DataGuard dataGuard(final Expr<BoolType> expr) {
		return new DataGuard(expr);
	}

	static ClockGuard clockGuard(final Expr<BoolType> expr) {
		return new ClockGuard(ClockConstrs.formExpr(expr));
	}

	public abstract Expr<BoolType> toExpr();

	public abstract boolean isDataGuard();

	public abstract boolean isClockGuard();

	public abstract DataGuard asDataGuard();

	public abstract ClockGuard asClockGuard();

	public static final class DataGuard extends Guard {
		private final Expr<BoolType> expr;

		private DataGuard(final Expr<BoolType> expr) {
			this.expr = checkNotNull(expr);
		}

		@Override
		public Expr<BoolType> toExpr() {
			return expr;
		}

		@Override
		public boolean isDataGuard() {
			return true;
		}

		@Override
		public boolean isClockGuard() {
			return false;
		}

		@Override
		public DataGuard asDataGuard() {
			return this;
		}

		@Override
		public ClockGuard asClockGuard() {
			throw new ClassCastException();
		}
	}

	public static final class ClockGuard extends Guard {
		private final ClockConstr clockConstr;

		private ClockGuard(final ClockConstr clockConstr) {
			this.clockConstr = checkNotNull(clockConstr);
		}

		public ClockConstr getClockConstr() {
			return clockConstr;
		}

		@Override
		public Expr<BoolType> toExpr() {
			return clockConstr.toExpr();
		}

		@Override
		public boolean isDataGuard() {
			return false;
		}

		@Override
		public boolean isClockGuard() {
			return true;
		}

		@Override
		public DataGuard asDataGuard() {
			throw new ClassCastException();
		}

		@Override
		public ClockGuard asClockGuard() {
			return this;
		}
	}

}
