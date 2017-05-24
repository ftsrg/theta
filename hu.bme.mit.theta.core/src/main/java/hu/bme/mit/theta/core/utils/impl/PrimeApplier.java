package hu.bme.mit.theta.core.utils.impl;

import static hu.bme.mit.theta.core.expr.Exprs.Prime;

import hu.bme.mit.theta.core.decl.Decl;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.expr.RefExpr;
import hu.bme.mit.theta.core.type.Type;

final class PrimeApplier {

	private PrimeApplier() {
	}

	static <T extends Type> Expr<T> applyPrimes(final Expr<T> expr, final VarIndexing indexing) {
		@SuppressWarnings("unchecked")
		final Expr<T> result = (Expr<T>) expr.accept(PrimeApplierVisitor.INSTANCE, indexing);
		return result;
	}

	private static class PrimeApplierVisitor extends ExprRewriterVisitor<VarIndexing> {
		private static final PrimeApplierVisitor INSTANCE = new PrimeApplierVisitor();

		private PrimeApplierVisitor() {
		}

		////////

		@Override
		public <DeclType extends Type> Expr<DeclType> visit(final RefExpr<DeclType> expr, final VarIndexing indexing) {
			final Decl<DeclType> decl = expr.getDecl();
			if (decl instanceof VarDecl) {
				final VarDecl<DeclType> var = (VarDecl<DeclType>) decl;
				final int index = indexing.get(var);
				if (index == 0) {
					return expr;
				} else {
					return Prime(expr, index);
				}
			} else {
				return expr;
			}
		}
	}

}
