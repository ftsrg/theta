package hu.bme.mit.inf.theta.formalism.common.expr;

import hu.bme.mit.inf.theta.core.expr.Expr;
import hu.bme.mit.inf.theta.core.type.Type;
import hu.bme.mit.inf.theta.formalism.common.type.PointerType;

public interface NewExpr<PointedType extends Type> extends Expr<PointerType<PointedType>> {

	public PointedType getPointedType();

}
