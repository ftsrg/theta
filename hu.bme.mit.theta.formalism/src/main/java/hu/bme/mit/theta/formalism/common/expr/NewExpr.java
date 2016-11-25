package hu.bme.mit.theta.formalism.common.expr;

import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.formalism.common.type.PointerType;

public interface NewExpr<PointedType extends Type> extends Expr<PointerType<PointedType>> {

	PointedType getPointedType();

}
