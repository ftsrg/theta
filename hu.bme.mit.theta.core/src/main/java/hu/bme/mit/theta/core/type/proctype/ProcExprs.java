package hu.bme.mit.theta.core.type.proctype;

import java.util.List;

import hu.bme.mit.theta.core.decl.ParamDecl;
import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.type.Type;

public final class ProcExprs {

	private ProcExprs() {
	}

	public static <ReturnType extends Type> ProcType<ReturnType> Proc(final List<? extends Type> paramTypes,
			final ReturnType returnType) {
		return new ProcType<>(paramTypes, returnType);
	}

	public static <ReturnType extends Type> ProcDecl<ReturnType> Proc(final String name,
			final List<? extends ParamDecl<? extends Type>> paramDecls, final ReturnType returnType) {
		return new ProcDecl<>(name, paramDecls, returnType);
	}

	public static <ReturnType extends Type> ProcCallExpr<ReturnType> Call(final Expr<ProcType<ReturnType>> proc,
			final Iterable<? extends Expr<?>> params) {
		return new ProcCallExpr<>(proc, params);
	}

}
