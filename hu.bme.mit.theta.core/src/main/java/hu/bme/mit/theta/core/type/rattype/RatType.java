package hu.bme.mit.theta.core.type.rattype;

import hu.bme.mit.theta.core.Expr;
import hu.bme.mit.theta.core.type.abstracttype.Additive;
import hu.bme.mit.theta.core.type.abstracttype.Equational;
import hu.bme.mit.theta.core.type.abstracttype.Multiplicative;
import hu.bme.mit.theta.core.type.abstracttype.Ordered;

public final class RatType
		implements Additive<RatType>, Multiplicative<RatType>, Equational<RatType>, Ordered<RatType> {

	private static final RatType INSTANCE = new RatType();
	private static final int HASH_SEED = 385863;
	private static final String TYPE_LABEL = "Rat";

	private RatType() {
	}

	static RatType getInstance() {
		return INSTANCE;
	}

	@Override
	public int hashCode() {
		return HASH_SEED;
	}

	@Override
	public boolean equals(final Object obj) {
		return (obj instanceof RatType);
	}

	@Override
	public String toString() {
		return TYPE_LABEL;
	}

	////

	@Override
	public RatAddExpr Add(final Expr<RatType> leftOp, final Expr<RatType> rightOp) {
		return RatExprs.Add(leftOp, rightOp);
	}

	@Override
	public RatSubExpr Sub(final Expr<RatType> leftOp, final Expr<RatType> rightOp) {
		return RatExprs.Sub(leftOp, rightOp);
	}

	@Override
	public RatNegExpr Neg(final Expr<RatType> op) {
		return RatExprs.Neg(op);
	}

	@Override
	public RatMulExpr Mul(final Expr<RatType> leftOp, final Expr<RatType> rightOp) {
		return RatExprs.Mul(leftOp, rightOp);
	}

	@Override
	public RatDivExpr Div(final Expr<RatType> leftOp, final Expr<RatType> rightOp) {
		return RatExprs.Div(leftOp, rightOp);
	}

	@Override
	public RatEqExpr Eq(final Expr<RatType> leftOp, final Expr<RatType> rightOp) {
		return RatExprs.Eq(leftOp, rightOp);
	}

	@Override
	public RatNeqExpr Neq(final Expr<RatType> leftOp, final Expr<RatType> rightOp) {
		return RatExprs.Neq(leftOp, rightOp);
	}

	@Override
	public RatLtExpr Lt(final Expr<RatType> leftOp, final Expr<RatType> rightOp) {
		return RatExprs.Lt(leftOp, rightOp);
	}

	@Override
	public RatLeqExpr Leq(final Expr<RatType> leftOp, final Expr<RatType> rightOp) {
		return RatExprs.Leq(leftOp, rightOp);
	}

	@Override
	public RatGtExpr Gt(final Expr<RatType> leftOp, final Expr<RatType> rightOp) {
		return RatExprs.Gt(leftOp, rightOp);
	}

	@Override
	public RatGeqExpr Geq(final Expr<RatType> leftOp, final Expr<RatType> rightOp) {
		return RatExprs.Geq(leftOp, rightOp);
	}

}
