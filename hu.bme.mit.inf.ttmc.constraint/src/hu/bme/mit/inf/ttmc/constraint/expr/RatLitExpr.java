package hu.bme.mit.inf.ttmc.constraint.expr;

import hu.bme.mit.inf.ttmc.constraint.type.RatType;

public interface RatLitExpr extends NullaryExpr<RatType> {
	public long getNum();
	public long getDenom();
}
