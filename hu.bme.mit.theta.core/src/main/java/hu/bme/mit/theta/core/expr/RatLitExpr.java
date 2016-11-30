package hu.bme.mit.theta.core.expr;

import hu.bme.mit.theta.core.type.RatType;

public interface RatLitExpr extends LitExpr<RatType>, NullaryExpr<RatType>, Comparable<RatLitExpr> {

	public int getNum();

	public int getDenom();

	public int sign();

	/**
	 * @return the largest integer less than or equal to the number
	 */
	public int floor();

	/**
	 * @return the smallest integer greater than or equal to the number
	 */
	public int ceil();

	public RatLitExpr add(final RatLitExpr that);

	public RatLitExpr sub(final RatLitExpr that);

	public RatLitExpr mul(final RatLitExpr that);

	public RatLitExpr div(final RatLitExpr that);

	public RatLitExpr abs();

	public RatLitExpr frac();

}
