package hu.bme.mit.theta.core.utils.impl;

import static hu.bme.mit.theta.core.expr.impl.Exprs.Prime;

import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.expr.VarRefExpr;
import hu.bme.mit.theta.core.type.Type;

final class PrimeApplier {

	private PrimeApplier() {
	}

	public static <T extends Type> Expr<T> applyPrimes(final Expr<T> expr, final VarIndexes indexes) {
		@SuppressWarnings("unchecked")
		final Expr<T> result = (Expr<T>) expr.accept(PrimeApplierVisitor.INSTANCE, indexes);
		return result;
	}

	private static class PrimeApplierVisitor extends ExprRewriterVisitor<VarIndexes> {
		private static final PrimeApplierVisitor INSTANCE = new PrimeApplierVisitor();

		private PrimeApplierVisitor() {
		}

		////////

		@Override
		public <DeclType extends Type> Expr<DeclType> visit(final VarRefExpr<DeclType> expr, final VarIndexes indexes) {
			final VarDecl<DeclType> varDecl = expr.getDecl();
			final int index = indexes.get(varDecl);
			if (index == 0) {
				return expr;
			} else {
				return Prime(expr, index);
			}
		}
	}

}
