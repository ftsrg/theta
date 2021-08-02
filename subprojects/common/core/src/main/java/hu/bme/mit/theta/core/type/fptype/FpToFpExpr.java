package hu.bme.mit.theta.core.type.fptype;

import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.UnaryExpr;
import hu.bme.mit.theta.core.utils.FpUtils;
import org.kframework.mpfr.BigFloat;

import static com.google.common.base.Preconditions.checkNotNull;

/**
 * signBits and signBitsificand is presumed to be unsignBitsed
 * Exponent is presumed to be signBitsed
 */
public class FpToFpExpr extends UnaryExpr<FpType, FpType> {
	private static final int HASH_SEED = 6799;
	private static final String OPERATOR_LABEL = "fptofp";

	private final Expr<FpType> op;
	private final int expBits;
	private final int signBits;

	private final FpRoundingMode roundingMode;

	private FpToFpExpr(final FpRoundingMode roundingMode, final Expr<FpType> op, final int expBits, final int signBits) {
		super(op);
		checkNotNull(op);
		this.op = op;

		this.signBits = signBits;
		this.expBits = expBits;

		checkNotNull(roundingMode);
		this.roundingMode = roundingMode;
	}

	public static FpToFpExpr of(final FpRoundingMode roundingMode, final Expr<FpType> op, final int exp, final int signBits) {
		return new FpToFpExpr(roundingMode, op, exp, signBits);
	}

	public static FpToFpExpr create(final FpRoundingMode roundingMode, final Expr<FpType> op, final int exp, final int signBits) {
		return FpToFpExpr.of(roundingMode, op, exp, signBits);
	}

	public int getExpBits() {
		return expBits;
	}

	public int getSignBits() {
		return signBits;
	}

	@Override
	public FpToFpExpr with(Expr<FpType> op) {
		if (op == getOp()) {
			return this;
		} else {
			return FpToFpExpr.of(roundingMode, op, expBits, signBits);
		}
	}

	@Override
	public FpType getType() {
		return FpType.of(expBits, signBits);
	}

	@Override
	public FpLitExpr eval(Valuation val) {
		final FpLitExpr op = (FpLitExpr) this.op.eval(val);

		BigFloat value = FpUtils.fpLitExprToBigFloat(roundingMode, op);
		return FpUtils.bigFloatToFpLitExpr(value, getType());
	}

	protected int getHashSeed() {
		return HASH_SEED;
	}

	public String getOperatorLabel() {
		return OPERATOR_LABEL;
	}

	public FpRoundingMode getRoundingMode() {
		return roundingMode;
	}
}
