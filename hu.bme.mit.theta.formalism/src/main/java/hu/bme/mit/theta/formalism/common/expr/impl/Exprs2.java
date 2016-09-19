package hu.bme.mit.theta.formalism.common.expr.impl;

import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.formalism.common.expr.DerefExpr;
import hu.bme.mit.theta.formalism.common.expr.NewExpr;
import hu.bme.mit.theta.formalism.common.expr.NullExpr;
import hu.bme.mit.theta.formalism.common.type.PointerType;

public final class Exprs2 {

	private static final NullExpr<?> NULL_EXPR;

	static {
		NULL_EXPR = new NullExprImpl<>();
	}

	private Exprs2() {
	}

	@SuppressWarnings("unchecked")
	public static <T extends Type> NullExpr<T> Null() {
		return (NullExpr<T>) NULL_EXPR;
	}

	public static <T extends Type> NewExpr<T> New(final T pointedType) {
		return new NewExprImpl<>(pointedType);
	}

	public static <T extends Type> DerefExpr<T> Deref(final Expr<? extends PointerType<? extends T>> op) {
		return new DerefExprImpl<>(op);
	}

}