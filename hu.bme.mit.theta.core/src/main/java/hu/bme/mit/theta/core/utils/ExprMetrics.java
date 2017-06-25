package hu.bme.mit.theta.core.utils;

import hu.bme.mit.theta.core.Expr;

final class ExprMetrics {

	private ExprMetrics() {
	}

	interface ExprMetric {
		int calculate(final Expr<?> expr);
	}

	static ExprMetric absoluteSize() {
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
