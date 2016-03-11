package hu.bme.mit.inf.ttmc.constraint.utils;

import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.type.Type;

public interface TypeInferrer {
	
	public <T extends Type> T getType(final Expr<T> expr);
	
}
