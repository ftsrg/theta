package hu.bme.mit.theta.core.type.inttype;

import hu.bme.mit.theta.core.Expr;
import hu.bme.mit.theta.core.Type;
import hu.bme.mit.theta.core.type.abstracttype.Additive;
import hu.bme.mit.theta.core.type.abstracttype.Castable;
import hu.bme.mit.theta.core.type.abstracttype.Equational;
import hu.bme.mit.theta.core.type.abstracttype.Multiplicative;
import hu.bme.mit.theta.core.type.abstracttype.Ordered;
import hu.bme.mit.theta.core.type.rattype.RatType;

public final class IntType implements Additive<IntType>, Multiplicative<IntType>, Equational<IntType>, Ordered<IntType>,
		Castable<IntType> {

	private static final IntType INSTANCE = new IntType();
	private static final int HASH_SEED = 222670;
	private static final String TYPE_LABEL = "Int";

	private IntType() {
	}

	static IntType getInstance() {
		return INSTANCE;
	}

	@Override
	public int hashCode() {
		return HASH_SEED;
	}

	@Override
	public boolean equals(final Object obj) {
		return (obj instanceof IntType);
	}

	@Override
	public String toString() {
		return TYPE_LABEL;
	}

	////

	@Override
	public IntAddExpr Add(final Iterable<? extends Expr<IntType>> ops) {
		return IntExprs.Add(ops);
	}

	@Override
	public IntSubExpr Sub(final Expr<IntType> leftOp, final Expr<IntType> rightOp) {
		return IntExprs.Sub(leftOp, rightOp);
	}

	@Override
	public IntNegExpr Neg(final Expr<IntType> op) {
		return IntExprs.Neg(op);
	}

	@Override
	public IntMulExpr Mul(final Iterable<? extends Expr<IntType>> ops) {
		return IntExprs.Mul(ops);
	}

	@Override
	public IntDivExpr Div(final Expr<IntType> leftOp, final Expr<IntType> rightOp) {
		return IntExprs.Div(leftOp, rightOp);
	}

	@Override
	public IntEqExpr Eq(final Expr<IntType> leftOp, final Expr<IntType> rightOp) {
		return IntExprs.Eq(leftOp, rightOp);
	}

	@Override
	public IntNeqExpr Neq(final Expr<IntType> leftOp, final Expr<IntType> rightOp) {
		return IntExprs.Neq(leftOp, rightOp);
	}

	@Override
	public IntLtExpr Lt(final Expr<IntType> leftOp, final Expr<IntType> rightOp) {
		return IntExprs.Lt(leftOp, rightOp);
	}

	@Override
	public IntLeqExpr Leq(final Expr<IntType> leftOp, final Expr<IntType> rightOp) {
		return IntExprs.Leq(leftOp, rightOp);
	}

	@Override
	public IntGtExpr Gt(final Expr<IntType> leftOp, final Expr<IntType> rightOp) {
		return IntExprs.Gt(leftOp, rightOp);
	}

	@Override
	public IntGeqExpr Geq(final Expr<IntType> leftOp, final Expr<IntType> rightOp) {
		return IntExprs.Geq(leftOp, rightOp);
	}

	@Override
	public <TargetType extends Type> Expr<TargetType> Cast(final Expr<IntType> op, final TargetType type) {
		if (type instanceof RatType) {
			@SuppressWarnings("unchecked")
			final Expr<TargetType> result = (Expr<TargetType>) IntExprs.ToRat(op);
			return result;
		} else {
			throw new ClassCastException("Int cannot be cast to " + type);
		}
	}

}
