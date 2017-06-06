package hu.bme.mit.theta.core.type.pointertype;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.theta.core.Expr;
import hu.bme.mit.theta.core.Type;

public final class PointerExprs {

	private PointerExprs() {
	}

	public static <PointedType extends Type> PointerType<PointedType> Pointer(final PointedType pointedType) {
		checkNotNull(pointedType);
		return new PointerType<>(pointedType);
	}

	public static <PointedType extends Type> NullExpr<PointedType> Null() {
		return NullExpr.getInstance();
	}

	public static <PointedType extends Type> NewExpr<PointedType> New(final PointedType pointedType) {
		return new NewExpr<>(pointedType);
	}

	public static <PointedType extends Type> DerefExpr<PointedType> Deref(final Expr<PointerType<PointedType>> op) {
		return new DerefExpr<>(op);
	}

}