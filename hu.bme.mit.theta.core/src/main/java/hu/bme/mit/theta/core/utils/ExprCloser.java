package hu.bme.mit.theta.core.utils;

import static hu.bme.mit.theta.core.decl.Decls.Param;
import static java.lang.String.format;

import java.util.Map;

import hu.bme.mit.theta.core.Decl;
import hu.bme.mit.theta.core.Expr;
import hu.bme.mit.theta.core.Type;
import hu.bme.mit.theta.core.decl.ParamDecl;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.anytype.RefExpr;

public final class ExprCloser {

	private static final String PARAM_NAME_FORMAT = "_%s_p";

	private ExprCloser() {
	}

	public static <T extends Type> Expr<T> close(final Expr<T> expr, final Map<VarDecl<?>, ParamDecl<?>> mapping) {
		if (expr instanceof RefExpr) {
			final RefExpr<T> ref = (RefExpr<T>) expr;
			final Decl<T> decl = ref.getDecl();
			if (decl instanceof VarDecl) {
				final VarDecl<T> var = (VarDecl<T>) decl;
				final ParamDecl<?> param = mapping.computeIfAbsent(var,
						v -> Param(format(PARAM_NAME_FORMAT, v.getName()), v.getType()));
				final Expr<T> paramRef = TypeUtils.cast(param.getRef(), expr.getType());
				return paramRef;
			}
		}

		return expr.map(op -> close(op, mapping));
	}

}
