package hu.bme.mit.theta.core.type.fptype;

import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.UnaryExpr;
import hu.bme.mit.theta.core.type.booltype.BoolExprs;
import hu.bme.mit.theta.core.type.booltype.BoolLitExpr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.type.booltype.OrExpr;

import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Or;
import static hu.bme.mit.theta.core.utils.TypeUtils.castFp;
import static hu.bme.mit.theta.core.utils.TypeUtils.checkAllTypesEqual;

public final class FpIsInfiniteExpr extends UnaryExpr<FpType, BoolType> {

	private static final int HASH_SEED = 1756;
	private static final String OPERATOR_LABEL = "isinfinite";

	private FpIsInfiniteExpr(final Expr<FpType> op) {
		super(op);
		checkAllTypesEqual(op);
	}

	public static FpIsInfiniteExpr of(final Expr<FpType> op) {
		return new FpIsInfiniteExpr(op);
	}

	public static FpIsInfiniteExpr create(final Expr<?> op) {
		final Expr<FpType> newOp = castFp(op);
		return FpIsInfiniteExpr.of(newOp);
	}

	@Override
	public UnaryExpr with(Expr op) {
		if (op == getOp()) {
			return this;
		} else {
			return FpIsInfiniteExpr.of(op);
		}
	}

	@Override
	public BoolType getType() {
		return Bool();
	}

	@Override
	public BoolLitExpr eval(final Valuation val) {
		final FpLitExpr opVal = (FpLitExpr) getOp().eval(val);

		OrExpr or = Or(Bool(opVal.isNegativeInfinity()), Bool(opVal.isPositiveInfinity()));
		final BoolLitExpr boolExpr = or.eval(val);
		return boolExpr;
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		} else if (obj instanceof FpIsInfiniteExpr) {
			final FpIsInfiniteExpr that = (FpIsInfiniteExpr) obj;
			return this.getOp().equals(that.getOp());
		} else {
			return false;
		}
	}

	@Override
	protected int getHashSeed() {
		return HASH_SEED;
	}

	@Override
	public String getOperatorLabel() {
		return OPERATOR_LABEL;
	}
}
 
