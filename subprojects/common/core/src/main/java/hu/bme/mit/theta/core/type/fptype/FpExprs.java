package hu.bme.mit.theta.core.type.fptype;

import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.bvtype.BvLitExpr;
import hu.bme.mit.theta.core.type.bvtype.BvType;

import java.util.Arrays;

public final class FpExprs {
	private FpExprs() {
	}

	public static FpType FpType(final int exponent, final int significand) {
		return FpType.of(exponent, significand);
	}

	public static FpLitExpr Fp(boolean hidden, BvLitExpr exponent, BvLitExpr significand) {
		return FpLitExpr.of(hidden, exponent, significand);
	}

	public static FpLitExpr NaN(final FpType fpType) {
		final var exponent = new boolean[fpType.getExponent()];
		Arrays.fill(exponent, true);
		final var significand = new boolean[fpType.getSignificand() - 1];
		Arrays.fill(significand, true);

		return Fp(false, BvLitExpr.of(exponent), BvLitExpr.of(significand));
	}

	public static FpLitExpr PositiveInfinity(final FpType fpType) {
		final var exponent = new boolean[fpType.getExponent()];
		Arrays.fill(exponent, true);
		final var significand = new boolean[fpType.getSignificand() - 1];
		Arrays.fill(significand, false);

		return Fp(false, BvLitExpr.of(exponent), BvLitExpr.of(significand));
	}

	public static FpLitExpr NegativeInfinity(final FpType fpType) {
		final var exponent = new boolean[fpType.getExponent()];
		Arrays.fill(exponent, true);
		final var significand = new boolean[fpType.getSignificand() - 1];
		Arrays.fill(significand, false);

		return Fp(true, BvLitExpr.of(exponent), BvLitExpr.of(significand));
	}

	public static FpLitExpr PositiveZero(final FpType fpType) {
		final var exponent = new boolean[fpType.getExponent()];
		Arrays.fill(exponent, false);
		final var significand = new boolean[fpType.getSignificand() - 1];
		Arrays.fill(significand, false);

		return Fp(false, BvLitExpr.of(exponent), BvLitExpr.of(significand));
	}

	public static FpLitExpr NegativeZero(final FpType fpType) {
		final var exponent = new boolean[fpType.getExponent()];
		Arrays.fill(exponent, false);
		final var significand = new boolean[fpType.getSignificand() - 1];
		Arrays.fill(significand, false);

		return Fp(true, BvLitExpr.of(exponent), BvLitExpr.of(significand));
	}

	public static FpAddExpr Add(final FpRoundingMode roundingMode, final Iterable<? extends Expr<FpType>> ops) {
		return FpAddExpr.of(roundingMode, ops);
	}

	public static FpSubExpr Sub(final FpRoundingMode roundingMode, final Expr<FpType> leftOp, final Expr<FpType> rightOp) {
		return FpSubExpr.of(roundingMode, leftOp, rightOp);
	}

	public static FpPosExpr Pos(final Expr<FpType> op) {
		return FpPosExpr.of(op);
	}

	public static FpNegExpr Neg(final Expr<FpType> op) {
		return FpNegExpr.of(op);
	}

	public static FpMulExpr Mul(final FpRoundingMode roundingMode, final Iterable<? extends Expr<FpType>> ops) {
		return FpMulExpr.of(roundingMode, ops);
	}

	public static FpDivExpr Div(final FpRoundingMode roundingMode, final Expr<FpType> leftOp, final Expr<FpType> rightOp) {
		return FpDivExpr.of(roundingMode, leftOp, rightOp);
	}

	public static FpRemExpr Rem(final Expr<FpType> leftOp, final Expr<FpType> rightOp) {
		return FpRemExpr.of(leftOp, rightOp);
	}

	public static FpAbsExpr Abs(final Expr<FpType> op) {
		return FpAbsExpr.of(op);
	}

	public static FpFromBvExpr FromBv(final FpRoundingMode roundingMode, final Expr<BvType> op, final FpType fpType, final boolean signed) {
		return FpFromBvExpr.of(roundingMode, op, fpType, signed);
	}

	public static FpEqExpr Eq(final Expr<FpType> leftOp, final Expr<FpType> rightOp) {
		return FpEqExpr.of(leftOp, rightOp);
	}

	public static FpAssignExpr FpAssign(final Expr<FpType> leftOp, final Expr<FpType> rightOp) {
		return FpAssignExpr.of(leftOp, rightOp);
	}

	public static FpNeqExpr Neq(final Expr<FpType> leftOp, final Expr<FpType> rightOp) {
		return FpNeqExpr.of(leftOp, rightOp);
	}

	public static FpGtExpr Gt(final Expr<FpType> leftOp, final Expr<FpType> rightOp) {
		return FpGtExpr.of(leftOp, rightOp);
	}

	public static FpGeqExpr Geq(final Expr<FpType> leftOp, final Expr<FpType> rightOp) {
		return FpGeqExpr.of(leftOp, rightOp);
	}

	public static FpLtExpr Lt(final Expr<FpType> leftOp, final Expr<FpType> rightOp) {
		return FpLtExpr.of(leftOp, rightOp);
	}

	public static FpLeqExpr Leq(final Expr<FpType> leftOp, final Expr<FpType> rightOp) {
		return FpLeqExpr.of(leftOp, rightOp);
	}

	public static FpIsNanExpr IsNan(final Expr<FpType> op) {
		return FpIsNanExpr.of(op);
	}

	public static FpIsInfiniteExpr IsInfinite(final Expr<FpType> op) {
		return FpIsInfiniteExpr.of(op);
	}

	public static FpRoundToIntegralExpr RoundToIntegral(final FpRoundingMode roundingMode, final Expr<FpType> op) {
		return FpRoundToIntegralExpr.of(roundingMode, op);
	}

	public static FpSqrtExpr Sqrt(final FpRoundingMode roundingMode, final Expr<FpType> op) {
		return FpSqrtExpr.of(roundingMode, op);
	}

	public static FpMaxExpr Max(final Expr<FpType> leftOp, final Expr<FpType> rightOp) {
		return FpMaxExpr.of(leftOp, rightOp);
	}

	public static FpMinExpr Min(final Expr<FpType> leftOp, final Expr<FpType> rightOp) {
		return FpMinExpr.of(leftOp, rightOp);
	}

	public static FpToBvExpr ToBv(final FpRoundingMode roundingMode, final Expr<FpType> op, final int size, final boolean sgn) {
		return FpToBvExpr.of(roundingMode, op, size, sgn);
	}

	public static FpToFpExpr ToFp(final FpRoundingMode roundingMode, final Expr<FpType> op, final int exp, final int sig) {
		return FpToFpExpr.of(roundingMode, op, exp, sig);
	}
}
