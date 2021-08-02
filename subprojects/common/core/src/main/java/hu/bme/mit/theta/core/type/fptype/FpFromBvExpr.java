package hu.bme.mit.theta.core.type.fptype;

import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.UnaryExpr;
import hu.bme.mit.theta.core.type.bvtype.BvLitExpr;
import hu.bme.mit.theta.core.type.bvtype.BvType;
import hu.bme.mit.theta.core.utils.BvUtils;
import hu.bme.mit.theta.core.utils.FpUtils;
import hu.bme.mit.theta.core.utils.TypeUtils;
import org.kframework.mpfr.BigFloat;

import java.math.BigInteger;
import java.util.List;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.theta.core.utils.TypeUtils.castFp;

/**
 * Sign and significand is presumed to be unsigned
 * Exponent is presumed to be signed
 */
public class FpFromBvExpr implements Expr<FpType> {
	private static final int HASH_SEED = 6696;
	private static final String OPERATOR_LABEL = "fpfrombv";

	private final Expr<BvType> sgn, sig, exp;

	private final FpRoundingMode roundingMode;

	private FpFromBvExpr(final FpRoundingMode roundingMode, final Expr<BvType> sgn, final Expr<BvType> sig, final Expr<BvType> exp) {
		checkNotNull(sgn);
		checkNotNull(sig);
		checkNotNull(exp);
		checkNotNull(roundingMode);
		this.sgn = sgn;
		this.sig = sig;
		this.exp = exp;
		this.roundingMode = roundingMode;
	}

	public static FpFromBvExpr of(final FpRoundingMode roundingMode, final Expr<BvType> sgn, final Expr<BvType> sig, final Expr<BvType> exp) {
		return new FpFromBvExpr(roundingMode, sgn, sig, exp);
	}

	public static FpFromBvExpr create(final FpRoundingMode roundingMode, final Expr<BvType> sgn, final Expr<BvType> sig, final Expr<BvType> exp) {
		return FpFromBvExpr.of(roundingMode, sgn, sig, exp);
	}

	public Expr<BvType> getSgn() {
		return sgn;
	}

	public Expr<BvType> getSig() {
		return sig;
	}

	public Expr<BvType> getExp() {
		return exp;
	}

	@Override
	public int getArity() {
		return 3;
	}

	@Override
	public FpType getType() {
		return FpType.of(sig.getType().getSize(), exp.getType().getSize());
	}

	@Override
	public FpLitExpr eval(Valuation val) {;
		final BvLitExpr sgnBv = (BvLitExpr) sgn.eval(val);
		final BvLitExpr sigBv = (BvLitExpr) sig.eval(val);
		final BvLitExpr expBv = (BvLitExpr) exp.eval(val);

		BigInteger sgnVal = BvUtils.unsignedBvLitExprToBigInteger(sgnBv);
		BigInteger sigVal = BvUtils.unsignedBvLitExprToBigInteger(sigBv);
		BigInteger expVal = BvUtils.signedBvLitExprToBigInteger(expBv);
		boolean sign = sgnVal.testBit(0);
		FpLitExpr fpLitExpr = FpUtils.bigFloatToFpLitExpr(new BigFloat(sign, sigVal, expVal.longValue(), FpUtils.getMathContext(getType(), roundingMode)),
				getType());
		return fpLitExpr;
	}

	@Override
	public List<? extends Expr<?>> getOps() {
		return List.of(sgn, sig, exp);
	}

	@Override
	public Expr<FpType> withOps(List<? extends Expr<?>> ops) {
		checkNotNull(ops);
		checkArgument(ops.size() == 3);
		final Expr<BvType> newSgn = TypeUtils.cast(ops.get(0), sgn.getType());
		final Expr<BvType> newSig = TypeUtils.cast(ops.get(1), sig.getType());
		final Expr<BvType> newExp = TypeUtils.cast(ops.get(2), exp.getType());
		return FpFromBvExpr.of(roundingMode, newSgn, newSig, newExp);
	}

	protected int getHashSeed() {
		return HASH_SEED;
	}

	public String getOperatorLabel() {
		return OPERATOR_LABEL;
	}
}
