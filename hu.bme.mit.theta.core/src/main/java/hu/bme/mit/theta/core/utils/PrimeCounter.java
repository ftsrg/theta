package hu.bme.mit.theta.core.utils;

import java.util.List;

import hu.bme.mit.theta.core.decl.Decl;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.type.anytype.PrimeExpr;
import hu.bme.mit.theta.core.type.anytype.RefExpr;

final class PrimeCounter {

	private PrimeCounter() {
	}

	public static VarIndexing countPrimes(final Expr<?> expr) {
		return collectPrimes(expr, 0).build();
	}

	private static VarIndexing.Builder collectPrimes(final Expr<?> expr, final int nPrimes) {
		if (expr instanceof RefExpr) {
			final RefExpr<?> ref = (RefExpr<?>) expr;
			final Decl<?> decl = ref.getDecl();
			if (decl instanceof VarDecl) {
				final VarDecl<?> var = (VarDecl<?>) decl;
				return VarIndexing.builder(0).inc(var, nPrimes);
			}
		}

		if (expr instanceof PrimeExpr<?>) {
			final PrimeExpr<?> primeExpr = (PrimeExpr<?>) expr;
			final Expr<?> op = primeExpr.getOp();
			return collectPrimes(op, nPrimes + 1);
		}

		final List<? extends Expr<?>> ops = expr.getOps();
		return ops.stream().map(op -> collectPrimes(op, nPrimes)).reduce(VarIndexing.builder(0),
				VarIndexing.Builder::join);
	}

}