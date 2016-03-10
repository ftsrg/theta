package hu.bme.mit.inf.ttmc.formalism.common.expr;

import hu.bme.mit.inf.ttmc.constraint.expr.UnaryExpr;
import hu.bme.mit.inf.ttmc.constraint.type.Type;

public interface PrimedExpr<ExprType extends Type> extends UnaryExpr<ExprType, ExprType> {
	
}
