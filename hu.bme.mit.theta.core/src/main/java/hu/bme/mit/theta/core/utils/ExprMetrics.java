package hu.bme.mit.theta.core.utils;

import hu.bme.mit.theta.core.Expr;

public final class ExprMetrics {

	private ExprMetrics() {
	}

	public interface ExprMetric {

		int calculate(final Expr<?> expr);

	}

	public static ExprMetric absoluteSize() {
		return new AbsoluteSize();
	}

	/////

	private final static class AbsoluteSize implements ExprMetric {

		@Override
		public int calculate(final Expr<?> expr) {
			return 1 + expr.getOps().stream().map(op -> calculate(op)).reduce(0, (x, y) -> x + y);
		}

	}
}
