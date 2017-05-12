package hu.bme.mit.theta.core.utils.impl;

import static hu.bme.mit.theta.core.decl.impl.Decls.Param;
import static java.lang.String.format;

import java.util.Map;

import hu.bme.mit.theta.core.decl.ParamDecl;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.expr.ParamRefExpr;
import hu.bme.mit.theta.core.expr.VarRefExpr;
import hu.bme.mit.theta.core.type.Type;

public final class ExprClosureHelper {

	private ExprClosureHelper() {
	}

	public static <T extends Type> Expr<T> close(final Expr<T> expr, final Map<VarDecl<?>, ParamDecl<?>> mapping) {
		@SuppressWarnings("unchecked")
		final Expr<T> result = (Expr<T>) expr.accept(ExprClosureVisitor.INSTANCE, mapping);
		return result;
	}

	private static final class ExprClosureVisitor extends ExprRewriterVisitor<Map<VarDecl<?>, ParamDecl<?>>> {
		private static final ExprClosureVisitor INSTANCE = new ExprClosureVisitor();
		private static final String PARAM_NAME_FORMAT = "_%s_p";

		private ExprClosureVisitor() {
		}

		@Override
		public <DeclType extends Type> ParamRefExpr<DeclType> visit(final VarRefExpr<DeclType> expr,
				final Map<VarDecl<?>, ParamDecl<?>> mapping) {
			final VarDecl<DeclType> varDecl = expr.getDecl();
			final ParamDecl<?> paramDecl = mapping.computeIfAbsent(varDecl,
					v -> Param(format(PARAM_NAME_FORMAT, v.getName()), v.getType()));
			@SuppressWarnings("unchecked")
			final ParamDecl<DeclType> castParamDecl = (ParamDecl<DeclType>) paramDecl;
			final ParamRefExpr<DeclType> result = castParamDecl.getRef();
			return result;
		}

	}

}
