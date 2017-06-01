package hu.bme.mit.theta.core.type.functype;

import hu.bme.mit.theta.core.decl.ParamDecl;
import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.type.Type;

public final class FuncExprs {

	private FuncExprs() {
	}

	public static <ParamType extends Type, ResultType extends Type> FuncType<ParamType, ResultType> Func(
			final ParamType paramType, final ResultType resultType) {
		return new FuncType<>(paramType, resultType);
	}

	public static <ParamType extends Type, ResultType extends Type> FuncLitExpr<ParamType, ResultType> Func(
			final ParamDecl<ParamType> paramDecl, final Expr<ResultType> result) {
		return new FuncLitExpr<>(paramDecl, result);
	}

	public static <ParamType extends Type, ResultType extends Type> FuncAppExpr<ParamType, ResultType> App(
			final Expr<FuncType<ParamType, ResultType>> func, final Expr<ParamType> param) {
		return new FuncAppExpr<>(func, param);
	}

}
