package hu.bme.mit.inf.theta.core.expr;

import hu.bme.mit.inf.theta.core.type.RatType;

public interface RatLitExpr extends LitExpr<RatType>, NullaryExpr<RatType>, Comparable<RatLitExpr> {

	public long getNum();

	public long getDenom();

}
