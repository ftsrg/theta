package hu.bme.mit.theta.formalism.common.expr;

import hu.bme.mit.theta.core.Expr;
import hu.bme.mit.theta.core.Type;
import hu.bme.mit.theta.formalism.common.type.PointerType;

public final class Exprs2 {

	private static final NullExpr<?> NULL_EXPR;

	static {
		NULL_EXPR = new NullExpr<>();
	}

	private Exprs2() {
	}

	@SuppressWarnings("unchecked")
	public static <T extends Type> NullExpr<T> Null() {
		return (NullExpr<T>) NULL_EXPR;
	}

	public static <T extends Type> NewExpr<T> New(final T pointedType) {
		return new NewExpr<>(pointedType);
	}

	public static <T extends Type> DerefExpr<T> Deref(final Expr<PointerType<? extends T>> op) {
		return new DerefExpr<>(op);
	}

}