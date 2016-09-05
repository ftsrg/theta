package hu.bme.mit.inf.theta.formalism.common.expr.impl;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.inf.theta.core.expr.Expr;
import hu.bme.mit.inf.theta.core.type.Type;
import hu.bme.mit.inf.theta.formalism.common.expr.DerefExpr;
import hu.bme.mit.inf.theta.formalism.common.expr.NewExpr;
import hu.bme.mit.inf.theta.formalism.common.expr.NullExpr;
import hu.bme.mit.inf.theta.formalism.common.expr.PrimedExpr;
import hu.bme.mit.inf.theta.formalism.common.type.PointerType;

public final class Exprs2 {

	private static final NullExpr<?> NULL_EXPR;

	static {
		NULL_EXPR = new NullExprImpl<>();
	}

	private Exprs2() {
	}

	public static <T extends Type> PrimedExpr<T> Prime(final Expr<? extends T> op) {
		checkNotNull(op);
		return new PrimedExprImpl<>(op);
	}

	@SuppressWarnings("unchecked")
	public static <T extends Type> NullExpr<T> Null() {
		return (NullExpr<T>) NULL_EXPR;
	}

	public static <T extends Type> NewExpr<T> New(final T pointedType) {
		checkNotNull(pointedType);
		return new NewExprImpl<>(pointedType);
	}

	public static <T extends Type> DerefExpr<T> Deref(final Expr<? extends PointerType<? extends T>> op) {
		checkNotNull(op);
		return new DerefExprImpl<>(op);
	}

}