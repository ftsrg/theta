package hu.bme.mit.theta.core.type.fptype;

import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.core.type.NullaryExpr;
import hu.bme.mit.theta.core.type.booltype.BoolExprs;
import hu.bme.mit.theta.core.type.booltype.BoolLitExpr;
import hu.bme.mit.theta.core.type.bvtype.BvLitExpr;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.theta.core.utils.FpUtils.bigFloatToFpLitExpr;
import static hu.bme.mit.theta.core.utils.FpUtils.fpLitExprToBigFloat;
import static hu.bme.mit.theta.core.utils.FpUtils.getMathContext;

public class FpLitExpr extends NullaryExpr<FpType> implements LitExpr<FpType>, Comparable<FpType> {
	private static final int HASH_SEED = 4254;
	private final boolean hidden;
	private final BvLitExpr exponent;
	private final BvLitExpr significand;
	private volatile int hashCode = 0;

	private FpLitExpr(final boolean hidden, final BvLitExpr exponent, final BvLitExpr significand) {
		checkNotNull(exponent);
		checkNotNull(significand);

		this.hidden = hidden;
		this.exponent = exponent;
		this.significand = significand;
	}

	public static FpLitExpr of(final boolean hidden, final BvLitExpr exponent, final BvLitExpr significand) {
		return new FpLitExpr(hidden, exponent, significand);
	}

	public boolean getHidden() {
		return hidden;
	}

	public BvLitExpr getExponent() {
		return exponent;
	}

	public BvLitExpr getSignificand() {
		return significand;
	}

	public boolean isNaN() {
		var isNaN = true;
		for (final var i : exponent.getValue()) {
			isNaN = isNaN && i;
		}
		var atLeastOne = false;
		for (final var i : significand.getValue()) {
			atLeastOne = atLeastOne || i;
		}
		return isNaN && atLeastOne;
	}

	public boolean isPositiveInfinity() {
		var isNaN = !hidden;
		for (final var i : exponent.getValue()) {
			isNaN = isNaN && i;
		}
		for (final var i : significand.getValue()) {
			isNaN = isNaN && !i;
		}
		return isNaN;
	}

	public boolean isNegativeInfinity() {
		var isNaN = hidden;
		for (final var i : exponent.getValue()) {
			isNaN = isNaN && i;
		}
		for (final var i : significand.getValue()) {
			isNaN = isNaN && !i;
		}
		return isNaN;
	}

	public boolean isNegativeZero() {
		var isNaN = !hidden;
		for (final var i : exponent.getValue()) {
			isNaN = isNaN && !i;
		}
		for (final var i : significand.getValue()) {
			isNaN = isNaN && !i;
		}
		return isNaN;
	}

	public boolean isPositiveZero() {
		var isNaN = hidden;
		for (final var i : exponent.getValue()) {
			isNaN = isNaN && !i;
		}
		for (final var i : significand.getValue()) {
			isNaN = isNaN && !i;
		}
		return isNaN;
	}

	public FpLitExpr add(final FpRoundingMode roundingMode, final FpLitExpr that) {
		checkArgument(this.getType().equals(that.getType()));
		var sum = fpLitExprToBigFloat(roundingMode, this).add(fpLitExprToBigFloat(roundingMode, that), getMathContext(this.getType(), roundingMode));
		return bigFloatToFpLitExpr(sum, getType());
	}

	public FpLitExpr sub(final FpRoundingMode roundingMode, final FpLitExpr that) {
		checkArgument(this.getType().equals(that.getType()));
		var sub = fpLitExprToBigFloat(roundingMode, this).subtract(fpLitExprToBigFloat(roundingMode, that), getMathContext(this.getType(), roundingMode));
		return bigFloatToFpLitExpr(sub, getType());
	}

	public FpLitExpr pos() {
		return this;
	}

	public FpLitExpr neg() {
		var neg = fpLitExprToBigFloat(FpRoundingMode.getDefaultRoundingMode(), this).negate();
		return bigFloatToFpLitExpr(neg, getType());
	}

	public FpLitExpr mul(final FpRoundingMode roundingMode, final FpLitExpr that) {
		checkArgument(this.getType().equals(that.getType()));
		var sub = fpLitExprToBigFloat(roundingMode, this).multiply(fpLitExprToBigFloat(roundingMode, that), getMathContext(this.getType(), roundingMode));
		return bigFloatToFpLitExpr(sub, getType());
	}

	public FpLitExpr div(final FpRoundingMode roundingMode, final FpLitExpr that) {
		checkArgument(this.getType().equals(that.getType()));
		var sub = fpLitExprToBigFloat(roundingMode, this).divide(fpLitExprToBigFloat(roundingMode, that), getMathContext(this.getType(), roundingMode));
		return bigFloatToFpLitExpr(sub, getType());
	}

	public BoolLitExpr eq(final FpLitExpr that) {
		checkArgument(this.getType().equals(that.getType()));
		var left = fpLitExprToBigFloat(FpRoundingMode.getDefaultRoundingMode(), this);
		var right = fpLitExprToBigFloat(FpRoundingMode.getDefaultRoundingMode(), that);
		if (left.isNaN() || right.isNaN()) {
			return BoolExprs.False();
		}
		return BoolExprs.Bool(this.hidden == that.hidden && this.exponent.equals(that.exponent) && this.significand.equals(that.significand));
	}

	public BoolLitExpr gt(final FpLitExpr that) {
		checkArgument(this.getType().equals(that.getType()));
		var left = fpLitExprToBigFloat(FpRoundingMode.getDefaultRoundingMode(), this);
		var right = fpLitExprToBigFloat(FpRoundingMode.getDefaultRoundingMode(), that);
		if (left.isNaN() || right.isNaN()) {
			return BoolExprs.False();
		}
		if (left.greaterThan(right)) {
			return BoolExprs.True();
		} else {
			return BoolExprs.False();
		}
	}

	public BoolLitExpr lt(final FpLitExpr that) {
		checkArgument(this.getType().equals(that.getType()));
		var left = fpLitExprToBigFloat(FpRoundingMode.getDefaultRoundingMode(), this);
		var right = fpLitExprToBigFloat(FpRoundingMode.getDefaultRoundingMode(), that);
		if (left.isNaN() || right.isNaN()) {
			return BoolExprs.False();
		}
		if (left.lessThan(right)) {
			return BoolExprs.True();
		} else {
			return BoolExprs.False();
		}
	}

	public BoolLitExpr geq(final FpLitExpr that) {
		checkArgument(this.getType().equals(that.getType()));
		var left = fpLitExprToBigFloat(FpRoundingMode.getDefaultRoundingMode(), this);
		var right = fpLitExprToBigFloat(FpRoundingMode.getDefaultRoundingMode(), that);
		if (left.isNaN() || right.isNaN()) {
			return BoolExprs.False();
		}
		if (left.greaterThanOrEqualTo(right)) {
			return BoolExprs.True();
		} else {
			return BoolExprs.False();
		}
	}

	public BoolLitExpr leq(final FpLitExpr that) {
		checkArgument(this.getType().equals(that.getType()));
		var left = fpLitExprToBigFloat(FpRoundingMode.getDefaultRoundingMode(), this);
		var right = fpLitExprToBigFloat(FpRoundingMode.getDefaultRoundingMode(), that);
		if (left.isNaN() || right.isNaN()) {
			return BoolExprs.False();
		}
		if (left.lessThanOrEqualTo(right)) {
			return BoolExprs.True();
		} else {
			return BoolExprs.False();
		}
	}

	public BoolLitExpr neq(final FpLitExpr that) {
		checkArgument(this.getType().equals(that.getType()));
		var left = fpLitExprToBigFloat(FpRoundingMode.getDefaultRoundingMode(), this);
		var right = fpLitExprToBigFloat(FpRoundingMode.getDefaultRoundingMode(), that);
		if (left.isNaN() || right.isNaN()) {
			return BoolExprs.False();
		}
		return BoolExprs.Bool(!(this.hidden == that.hidden && this.exponent.equals(that.exponent) && this.significand.equals(that.significand)));
	}

	@Override
	public FpType getType() {
		return FpType.of(exponent.getType().getSize(), significand.getType().getSize() + 1);
	}

	@Override
	public LitExpr<FpType> eval(Valuation val) {
		return this;
	}

	@Override
	public int hashCode() {
		int result = hashCode;
		if (result == 0) {
			result = HASH_SEED;
			result = 31 * result + Boolean.hashCode(hidden);
			result = 31 * result + exponent.hashCode();
			result = 31 * result + significand.hashCode();
			hashCode = result;
		}
		return result;
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		} else if (obj instanceof FpLitExpr && getType().equals(((FpLitExpr) obj).getType())) {
			return eq((FpLitExpr) obj).equals(BoolExprs.True());
		} else {
			return false;
		}
	}

	@Override
	public String toString() {
		return
				(hidden ? "-" : "+") +
						exponent.toString() +
						"." +
						significand.toString();
	}

	@Override
	public int compareTo(FpType fpType) {
		return 0;
	}
}
