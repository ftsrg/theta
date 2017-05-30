package hu.bme.mit.theta.core.type.proctype;

import java.util.List;

import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.type.ProcType;
import hu.bme.mit.theta.core.type.Type;

public final class ProcExprs {

	private ProcExprs() {
	}

	public static <ReturnType extends Type> ProcCallExpr<ReturnType> Call(
			final Expr<? extends ProcType<? extends ReturnType>> proc, final List<? extends Expr<?>> params) {
		return new ProcCallExpr<>(proc, params);
	}

}
