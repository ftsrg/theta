package hu.bme.mit.inf.ttmc.formalism.common.expr;

import hu.bme.mit.inf.ttmc.core.expr.UnaryExpr;
import hu.bme.mit.inf.ttmc.core.type.Type;
import hu.bme.mit.inf.ttmc.formalism.common.type.PointerType;

public interface DerefExpr<PointedType extends Type>
		extends UnaryExpr<PointerType<? extends PointedType>, PointedType> {
}
