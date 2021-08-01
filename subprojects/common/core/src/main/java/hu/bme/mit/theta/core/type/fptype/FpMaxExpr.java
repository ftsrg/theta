package hu.bme.mit.theta.core.type.fptype;

import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.BinaryExpr;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.core.type.UnaryExpr;
import hu.bme.mit.theta.core.type.inttype.IntLitExpr;
import hu.bme.mit.theta.core.type.inttype.IntRemExpr;
import hu.bme.mit.theta.core.type.inttype.IntType;
import hu.bme.mit.theta.core.utils.FpUtils;
import hu.bme.mit.theta.core.utils.TypeUtils;

import java.math.RoundingMode;
import java.util.List;

import static com.google.common.base.Preconditions.checkNotNull;
import static com.google.common.collect.ImmutableList.toImmutableList;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;
import static hu.bme.mit.theta.core.utils.TypeUtils.*;

public class FpMaxExpr extends BinaryExpr<FpType, FpType> {
	private static final int HASH_SEED = 6668;
	private static final String OPERATOR_LABEL = "fpmax";

	private final FpRoundingMode roundingMode;

	private FpMaxExpr(final FpRoundingMode roundingMode, final Expr<FpType> leftOp, final Expr<FpType> rightOp) {
		super(leftOp, rightOp);
		checkAllTypesEqual(leftOp, rightOp);
		checkNotNull(roundingMode);
		this.roundingMode = roundingMode;
	}

	public static FpMaxExpr of(final FpRoundingMode roundingMode, final Expr<FpType> leftOp, final Expr<FpType> rightOp) {
		return new FpMaxExpr(roundingMode, leftOp, rightOp);
	}

	public static FpMaxExpr create(final FpRoundingMode roundingMode, final Expr<FpType> leftOp, final Expr<FpType> rightOp) {
		checkNotNull(leftOp, rightOp);
		final Expr<FpType> newLeftOp = castFp(leftOp);
		final Expr<FpType> newRightOp = castFp(rightOp);
		return FpMaxExpr.of(roundingMode, newLeftOp, newRightOp);
	}

	@Override
	public BinaryExpr<FpType, FpType> with(Expr<FpType> leftOp, Expr<FpType> rightOp) {
		if (leftOp == getLeftOp() && rightOp == getRightOp()) {
			return this;
		} else {
			return FpMaxExpr.of(roundingMode, leftOp, rightOp);
		}
	}

	@Override
	public BinaryExpr<FpType, FpType> withLeftOp(Expr<FpType> leftOp) {
		return with(leftOp, getRightOp());
	}

	@Override
	public BinaryExpr<FpType, FpType> withRightOp(Expr<FpType> rightOp) {
		return with(getLeftOp(), rightOp);
	}

	@Override
	protected int getHashSeed() {
		return HASH_SEED;
	}

	@Override
	public String getOperatorLabel() {
		return OPERATOR_LABEL;
	}

	@Override
	public FpType getType() {
		return getLeftOp().getType();
	}

	@Override
	public LitExpr<FpType> eval(Valuation val) {
		final FpLitExpr leftOpVal = (FpLitExpr) getLeftOp().eval(val);
		final FpLitExpr rightOpVal = (FpLitExpr) getRightOp().eval(val);
		if(FpUtils.fpLitExprToBigFloat(roundingMode, leftOpVal).greaterThan(FpUtils.fpLitExprToBigFloat(roundingMode, rightOpVal))) {
			return leftOpVal;
		} else {
			return rightOpVal;
		}
	}
}
