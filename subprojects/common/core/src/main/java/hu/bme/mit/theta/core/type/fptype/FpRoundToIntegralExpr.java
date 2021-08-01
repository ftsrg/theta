package hu.bme.mit.theta.core.type.fptype;

import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.core.type.UnaryExpr;
import hu.bme.mit.theta.core.utils.FpUtils;
import hu.bme.mit.theta.core.utils.TypeUtils;
import org.kframework.mpfr.BigFloat;
import org.kframework.mpfr.BinaryMathContext;

import java.util.List;

import static com.google.common.base.Preconditions.checkNotNull;
import static com.google.common.collect.ImmutableList.toImmutableList;
import static hu.bme.mit.theta.core.utils.TypeUtils.castFp;
import static hu.bme.mit.theta.core.utils.TypeUtils.checkAllTypesEqual;

public class FpRoundToIntegralExpr extends UnaryExpr<FpType, FpType> { // round to integral
	private static final int HASH_SEED = 6671;
	private static final String OPERATOR_LABEL = "fpfloor";

	private final FpRoundingMode roundingMode;

	private FpRoundToIntegralExpr(final FpRoundingMode roundingMode, final Expr<FpType> op) {
		super(op);
		checkNotNull(roundingMode);
		this.roundingMode = roundingMode;
	}

	public static FpRoundToIntegralExpr of(final FpRoundingMode roundingMode, Expr<FpType> op) {
		return new FpRoundToIntegralExpr(roundingMode, op);
	}

	public static FpRoundToIntegralExpr create(final FpRoundingMode roundingMode, Expr<?> op) {
		checkNotNull(op);
		return FpRoundToIntegralExpr.of(roundingMode, castFp(op));
	}

	public FpRoundingMode getRoundingMode() {
		return roundingMode;
	}

	@Override
	public FpType getType() {
		return getOp().getType();
	}

	@Override
	public FpLitExpr eval(Valuation val) {
		final FpLitExpr opVal = (FpLitExpr) getOp().eval(val);
		BigFloat round = FpUtils.fpLitExprToBigFloat(FpRoundingMode.getDefaultRoundingMode(), opVal)
				.round(FpUtils.getMathContext(this.getType(), roundingMode));
		if(opVal.getHidden()) {
			round.negate();
		}
		return FpUtils.bigFloatToFpLitExpr(round, this.getType());
	}

	@Override
	public FpRoundToIntegralExpr with(final Expr<FpType> op) {
		if (op == getOp()) {
			return this;
		} else {
			return FpRoundToIntegralExpr.of(roundingMode, op);
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
