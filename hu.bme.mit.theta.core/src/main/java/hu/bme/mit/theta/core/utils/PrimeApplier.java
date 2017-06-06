package hu.bme.mit.theta.core.utils;

import static hu.bme.mit.theta.core.type.anytype.Exprs.Prime;

import hu.bme.mit.theta.core.Decl;
import hu.bme.mit.theta.core.Expr;
import hu.bme.mit.theta.core.Type;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.anytype.RefExpr;

final class PrimeApplier {

	private PrimeApplier() {
	}

	static <T extends Type> Expr<T> applyPrimes(final Expr<T> expr, final VarIndexing indexing) {
		if (expr instanceof RefExpr) {
			final RefExpr<T> ref = (RefExpr<T>) expr;
			final Decl<T> decl = ref.getDecl();
			if (decl instanceof VarDecl) {
				final VarDecl<T> var = (VarDecl<T>) decl;
				final int index = indexing.get(var);
				if (index == 0) {
					return expr;
				} else {
					return Prime(expr, index);
				}
			}
		}

		return expr.rewrite(op -> applyPrimes(op, indexing));
	}

}
