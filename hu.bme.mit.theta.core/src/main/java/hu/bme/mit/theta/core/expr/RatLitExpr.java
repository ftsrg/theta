package hu.bme.mit.theta.core.expr;

import hu.bme.mit.theta.core.type.RatType;

public interface RatLitExpr extends LitExpr<RatType>, NullaryExpr<RatType>, Comparable<RatLitExpr> {

	long getNum();

	long getDenom();

}
