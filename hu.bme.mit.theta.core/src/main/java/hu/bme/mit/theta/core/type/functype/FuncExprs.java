package hu.bme.mit.theta.core.type.functype;

import hu.bme.mit.theta.core.decl.ParamDecl;
import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.type.Type;

public final class FuncExprs {

	private FuncExprs() {
	}

	public static <P extends Type, R extends Type> FuncType<P, R> Func(final P paramType, final R resultType) {
		return new FuncType<>(paramType, resultType);
	}

	public static <P extends Type, R extends Type> FuncLitExpr<? super P, ? extends R> Func(
			final ParamDecl<? super P> paramDecl, final Expr<? extends R> result) {
		return new FuncLitExpr<P, R>(paramDecl, result);
	}

	public static <P extends Type, R extends Type> FuncAppExpr<P, R> App(
			final Expr<? extends FuncType<? super P, ? extends R>> func, final Expr<? extends P> param) {
		return new FuncAppExpr<>(func, param);
	}

}
