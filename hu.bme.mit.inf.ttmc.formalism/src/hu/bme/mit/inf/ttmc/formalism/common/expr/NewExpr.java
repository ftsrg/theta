package hu.bme.mit.inf.ttmc.formalism.common.expr;

import hu.bme.mit.inf.ttmc.core.expr.Expr;
import hu.bme.mit.inf.ttmc.core.type.Type;
import hu.bme.mit.inf.ttmc.formalism.common.type.PointerType;

public interface NewExpr<PointedType extends Type> extends Expr<PointerType<PointedType>> {

	public PointedType getPointedType();

}
