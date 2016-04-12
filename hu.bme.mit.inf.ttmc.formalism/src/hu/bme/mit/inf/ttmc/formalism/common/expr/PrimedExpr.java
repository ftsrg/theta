package hu.bme.mit.inf.ttmc.formalism.common.expr;

import hu.bme.mit.inf.ttmc.core.expr.UnaryExpr;
import hu.bme.mit.inf.ttmc.core.type.Type;

public interface PrimedExpr<ExprType extends Type> extends UnaryExpr<ExprType, ExprType> {
	
}
