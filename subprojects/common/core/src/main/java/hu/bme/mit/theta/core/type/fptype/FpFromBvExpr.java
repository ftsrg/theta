package hu.bme.mit.theta.core.type.fptype;

import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.UnaryExpr;
import hu.bme.mit.theta.core.type.bvtype.BvLitExpr;
import hu.bme.mit.theta.core.type.bvtype.BvType;
import hu.bme.mit.theta.core.utils.BvUtils;
import hu.bme.mit.theta.core.utils.FpUtils;
import org.kframework.mpfr.BigFloat;
import org.kframework.mpfr.BinaryMathContext;

import static com.google.common.base.Preconditions.checkNotNull;

public class FpFromBvExpr extends UnaryExpr<BvType, FpType> {
	private static final int HASH_SEED = 6696;
	private static final String OPERATOR_LABEL = "fpfrombv";

	private final FpRoundingMode roundingMode;
	private final FpType fpType;
	private final boolean signed;

	private FpFromBvExpr(final FpRoundingMode roundingMode, final Expr<BvType> op, final FpType fpType, final boolean signed) {
		super(op);
		this.fpType = fpType;
		this.signed = signed;
		checkNotNull(roundingMode);
		this.roundingMode = roundingMode;
	}

	public static FpFromBvExpr of(final FpRoundingMode roundingMode, final Expr<BvType> op, final FpType fpType, final boolean signed) {
		return new FpFromBvExpr(roundingMode, op, fpType, signed);
	}

	public static FpFromBvExpr create(final FpRoundingMode roundingMode, final Expr<BvType> op, final FpType fpType, final boolean signed) {
		return FpFromBvExpr.of(roundingMode, op, fpType, signed);
	}

	public FpRoundingMode getRoundingMode() {
		return roundingMode;
	}

	public FpType getFpType() {
		return fpType;
	}

	public boolean isSigned() {
		return signed;
	}

	@Override
	public FpType getType() {
		return fpType;
	}

	@Override
	public FpLitExpr eval(Valuation val) {
		BinaryMathContext mathContext = FpUtils.getMathContext(fpType, FpRoundingMode.RNE);
		BvLitExpr eval = (BvLitExpr) getOp().eval(val);
		return FpUtils.bigFloatToFpLitExpr(new BigFloat(signed ? BvUtils.signedBvLitExprToBigInteger(eval) : BvUtils.unsignedBvLitExprToBigInteger(eval), mathContext), fpType);
	}


	@Override
	public FpFromBvExpr with(Expr<BvType> op) {
		return new FpFromBvExpr(roundingMode, op, fpType, signed);
	}

	protected int getHashSeed() {
		return HASH_SEED;
	}

	public String getOperatorLabel() {
		return OPERATOR_LABEL;
	}
}
