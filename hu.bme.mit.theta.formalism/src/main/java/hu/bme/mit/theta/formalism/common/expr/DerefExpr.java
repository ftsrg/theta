package hu.bme.mit.theta.formalism.common.expr;

import hu.bme.mit.theta.core.expr.UnaryExpr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.formalism.common.type.PointerType;

public interface DerefExpr<PointedType extends Type>
		extends UnaryExpr<PointerType<? extends PointedType>, PointedType> {
}
