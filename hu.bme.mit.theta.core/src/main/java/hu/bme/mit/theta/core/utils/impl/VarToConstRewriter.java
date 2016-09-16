package hu.bme.mit.theta.core.utils.impl;

import hu.bme.mit.theta.core.decl.ConstDecl;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.expr.ConstRefExpr;
import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.expr.VarRefExpr;
import hu.bme.mit.theta.core.type.Type;

public class VarToConstRewriter {

	private static final VarToConstVisitor VISITOR;

	static {
		VISITOR = new VarToConstVisitor();
	}

	private VarToConstRewriter() {
	}

	public static <T extends Type> Expr<T> rewrite(final Expr<T> expr, final VarIndexes indexes) {
		@SuppressWarnings("unchecked")
		final Expr<T> result = (Expr<T>) expr.accept(VISITOR, indexes);
		return result;
	}

	private static class VarToConstVisitor extends ExprRewriterVisitor<VarIndexes> {

		private VarToConstVisitor() {
		}

		////////

		@Override
		public <DeclType extends Type> ConstRefExpr<DeclType> visit(final VarRefExpr<DeclType> expr,
				final VarIndexes indexes) {
			final VarDecl<DeclType> varDecl = expr.getDecl();
			final int index = indexes.get(varDecl);

			final ConstDecl<DeclType> constDecl = varDecl.getConstDecl(index);
			final ConstRefExpr<DeclType> constRef = constDecl.getRef();

			return constRef;
		}
	}

}
