package hu.bme.mit.inf.theta.constraint.ui.transform;

import hu.bme.mit.inf.theta.constraint.model.Expression;
import hu.bme.mit.inf.theta.core.expr.Expr;
import hu.bme.mit.inf.theta.core.type.Type;

public interface ExprTransformator {

	public Expr<? extends Type> transform(Expression expression);

}
