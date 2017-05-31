package hu.bme.mit.theta.core.type;

import hu.bme.mit.theta.core.expr.LitExpr;

public interface Type {

	LitExpr<? extends Type> getAny();

}
