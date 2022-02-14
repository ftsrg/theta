package hu.bme.mit.theta.core.utils;

import com.google.common.collect.ImmutableSet;
import hu.bme.mit.theta.common.OsHelper;
import hu.bme.mit.theta.core.type.fptype.FpAbsExpr;
import hu.bme.mit.theta.core.type.fptype.FpAddExpr;
import hu.bme.mit.theta.core.type.fptype.FpDivExpr;
import hu.bme.mit.theta.core.type.fptype.FpEqExpr;
import hu.bme.mit.theta.core.type.fptype.FpFromBvExpr;
import hu.bme.mit.theta.core.type.fptype.FpGeqExpr;
import hu.bme.mit.theta.core.type.fptype.FpGtExpr;
import hu.bme.mit.theta.core.type.fptype.FpIsNanExpr;
import hu.bme.mit.theta.core.type.fptype.FpLeqExpr;
import hu.bme.mit.theta.core.type.fptype.FpLitExpr;
import hu.bme.mit.theta.core.type.fptype.FpLtExpr;
import hu.bme.mit.theta.core.type.fptype.FpMaxExpr;
import hu.bme.mit.theta.core.type.fptype.FpMinExpr;
import hu.bme.mit.theta.core.type.fptype.FpMulExpr;
import hu.bme.mit.theta.core.type.fptype.FpNegExpr;
import hu.bme.mit.theta.core.type.fptype.FpNeqExpr;
import hu.bme.mit.theta.core.type.fptype.FpPosExpr;
import hu.bme.mit.theta.core.type.fptype.FpRemExpr;
import hu.bme.mit.theta.core.type.fptype.FpRoundToIntegralExpr;
import hu.bme.mit.theta.core.type.fptype.FpSqrtExpr;
import hu.bme.mit.theta.core.type.fptype.FpSubExpr;
import hu.bme.mit.theta.core.type.fptype.FpToBvExpr;
import hu.bme.mit.theta.core.type.fptype.FpToFpExpr;
import org.kframework.mpfr.BigFloat;
import org.kframework.mpfr.BinaryMathContext;

import java.math.BigInteger;
import java.util.Arrays;
import java.util.Collection;
import java.util.List;
import java.util.stream.Stream;

import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool;
import static hu.bme.mit.theta.core.type.fptype.FpExprs.Abs;
import static hu.bme.mit.theta.core.type.fptype.FpExprs.Add;
import static hu.bme.mit.theta.core.type.fptype.FpExprs.Div;
import static hu.bme.mit.theta.core.type.fptype.FpExprs.Eq;
import static hu.bme.mit.theta.core.type.fptype.FpExprs.FpType;
import static hu.bme.mit.theta.core.type.fptype.FpExprs.FromBv;
import static hu.bme.mit.theta.core.type.fptype.FpExprs.Geq;
import static hu.bme.mit.theta.core.type.fptype.FpExprs.Gt;
import static hu.bme.mit.theta.core.type.fptype.FpExprs.IsNan;
import static hu.bme.mit.theta.core.type.fptype.FpExprs.Leq;
import static hu.bme.mit.theta.core.type.fptype.FpExprs.Lt;
import static hu.bme.mit.theta.core.type.fptype.FpExprs.Max;
import static hu.bme.mit.theta.core.type.fptype.FpExprs.Min;
import static hu.bme.mit.theta.core.type.fptype.FpExprs.Mul;
import static hu.bme.mit.theta.core.type.fptype.FpExprs.Neg;
import static hu.bme.mit.theta.core.type.fptype.FpExprs.Neq;
import static hu.bme.mit.theta.core.type.fptype.FpExprs.Pos;
import static hu.bme.mit.theta.core.type.fptype.FpExprs.Rem;
import static hu.bme.mit.theta.core.type.fptype.FpExprs.RoundToIntegral;
import static hu.bme.mit.theta.core.type.fptype.FpExprs.Sqrt;
import static hu.bme.mit.theta.core.type.fptype.FpExprs.Sub;
import static hu.bme.mit.theta.core.type.fptype.FpExprs.ToBv;
import static hu.bme.mit.theta.core.type.fptype.FpExprs.ToFp;
import static hu.bme.mit.theta.core.type.fptype.FpRoundingMode.RNA;
import static hu.bme.mit.theta.core.type.fptype.FpRoundingMode.RNE;
import static hu.bme.mit.theta.core.type.fptype.FpRoundingMode.RTZ;

public class FpTestUtils {

	private static final BinaryMathContext BINARY16 = BinaryMathContext.BINARY16.withRoundingMode(FpUtils.getMathContextRoundingMode(RNE));
	private static final BinaryMathContext BINARY32 = BinaryMathContext.BINARY32.withRoundingMode(FpUtils.getMathContextRoundingMode(RNE));
	private static final BinaryMathContext BINARY64 = BinaryMathContext.BINARY64.withRoundingMode(FpUtils.getMathContextRoundingMode(RNE));

	private FpTestUtils() {
	}

	public static Stream<?> GetOperations() {
		return Stream.concat(
				Stream.concat(
						BasicOperations().stream(),
						Stream.concat(
								LinuxSpecificTests().stream(),
								WindowsSpecificTests().stream())),
				Stream.concat(
						NaNOperations().stream(),
						InfinityOperations().stream()
				));
	}

	private static Collection<?> BasicOperations() {
		return Arrays.asList(new Object[][]{
				{FpAddExpr.class, Fp16("5.5"), Add(RNE, List.of(Fp16("2.1"), Fp16("3.4")))},
				{FpSubExpr.class, Fp16("2.1"), Sub(RNE, Fp16("5.5"), Fp16("3.4"))},
				{FpPosExpr.class, Fp16("2.1"), Pos(Fp16("2.1"))},
				{FpNegExpr.class, Fp16("-2.1"), Neg(Fp16("2.1"))},
				{FpMulExpr.class, Fp16("7.14"), Mul(RNE, List.of(Fp16("2.1"), Fp16("3.4")))},
				{FpDivExpr.class, Fp16("2.1"), Div(RNE, Fp16("7.14"), Fp16("3.4"))},
				{FpEqExpr.class, Bool(true), Eq(Fp16("7.14"), Fp16("7.14"))},
				{FpEqExpr.class, Bool(false), Eq(Fp16("7.14"), Fp16("7.15"))},
				{FpNeqExpr.class, Bool(true), Neq(Fp16("-7.14"), Fp16("7.14"))},
				{FpNeqExpr.class, Bool(false), Neq(Fp16("-7.14"), Fp16("-7.14"))},
				{FpAbsExpr.class, Fp16("2.1"), Abs(Fp16("2.1"))},
				{FpAbsExpr.class, Fp16("2.1"), Abs(Fp16("-2.1"))},
				{FpGeqExpr.class, Bool(true), Geq(Fp16("7.15"), Fp16("7.14"))},
				{FpGeqExpr.class, Bool(true), Geq(Fp16("7.14"), Fp16("7.14"))},
				{FpGeqExpr.class, Bool(false), Geq(Fp16("-7.15"), Fp16("-7.14"))},
				{FpGtExpr.class, Bool(true), Gt(Fp16("7.15"), Fp16("7.14"))},
				{FpGtExpr.class, Bool(false), Gt(Fp16("7.14"), Fp16("7.14"))},
				{FpGtExpr.class, Bool(false), Gt(Fp16("-7.15"), Fp16("-7.14"))},
				{FpIsNanExpr.class, Bool(true), IsNan(Fp16NaN())},
				{FpIsNanExpr.class, Bool(false), IsNan(Fp16PInf())},
				{FpIsNanExpr.class, Bool(false), IsNan(Fp16NInf())},
				{FpIsNanExpr.class, Bool(false), IsNan(Fp16("0.0"))},
				{FpLeqExpr.class, Bool(true), Leq(Fp16("7.14"), Fp16("7.15"))},
				{FpLeqExpr.class, Bool(true), Leq(Fp16("7.14"), Fp16("7.14"))},
				{FpLeqExpr.class, Bool(false), Leq(Fp16("-7.14"), Fp16("-7.15"))},
				{FpLtExpr.class, Bool(true), Lt(Fp16("7.14"), Fp16("7.15"))},
				{FpLtExpr.class, Bool(false), Lt(Fp16("7.14"), Fp16("7.14"))},
				{FpLtExpr.class, Bool(false), Lt(Fp16("-7.14"), Fp16("-7.15"))},
				{FpMaxExpr.class, Fp16("2.1"), Max(Fp16("-2.1"), Fp16("2.1"))},
				{FpMaxExpr.class, Fp16("2.1"), Max(Fp16("1.9"), Fp16("2.1"))},
				{FpMinExpr.class, Fp16("-2.1"), Min(Fp16("-2.1"), Fp16("2.1"))},
				{FpMinExpr.class, Fp16("1.9"), Min(Fp16("1.9"), Fp16("2.1"))},
				{FpRemExpr.class, Fp16("0.1"), Rem(Fp16("4.3"), Fp16("2.1"))},
				{FpRemExpr.class, Fp16("-0.1"), Rem(Fp16("-4.3"), Fp16("2.1"))},
				{FpRemExpr.class, Fp16("0.1"), Rem(Fp16("4.3"), Fp16("-2.1"))},
				{FpRemExpr.class, Fp16("-0.1"), Rem(Fp16("-4.3"), Fp16("-2.1"))},
				{FpRoundToIntegralExpr.class, Fp16("2.0"), RoundToIntegral(RNE, Fp16("2.49"))},
				{FpRoundToIntegralExpr.class, Fp16("-10.0"), RoundToIntegral(RNE, Fp16("-10.49"))},
				{FpSqrtExpr.class, Fp16("2.1"), Sqrt(RNE, Fp16("4.41"))},
				{FpSqrtExpr.class, Fp16("3.0"), Sqrt(RNE, Fp16("9.0"))},
				{FpSqrtExpr.class, Fp16("0.1"), Sqrt(RNE, Fp16("0.01"))},
				{FpToBvExpr.class, BvUtils.bigIntegerToUnsignedBvLitExpr(BigInteger.TEN, 16), ToBv(RTZ, Fp16("10.9"), 16, false)},
				{FpToBvExpr.class, BvUtils.bigIntegerToUnsignedBvLitExpr(BigInteger.TEN, 3), ToBv(RTZ, Fp16("10.9"), 3, false)},
				{FpToBvExpr.class, BvUtils.bigIntegerToSignedBvLitExpr(BigInteger.TEN, 16), ToBv(RTZ, Fp16("10.9"), 16, true)},
				{FpToBvExpr.class, BvUtils.bigIntegerToSignedBvLitExpr(BigInteger.TEN, 4), ToBv(RTZ, Fp16("10.9"), 4, true)},
				{FpToBvExpr.class, BvUtils.bigIntegerToSignedBvLitExpr(BigInteger.TEN.negate(), 16), ToBv(RTZ, Fp16("-10.9"), 16, true)},
				{FpToBvExpr.class, BvUtils.bigIntegerToSignedBvLitExpr(BigInteger.TEN.negate(), 4), ToBv(RTZ, Fp16("-10.9"), 4, true)},
				{FpToFpExpr.class, Fp32("12.0"), ToFp(RNE, Fp16("12.0"), 8, 24)},
				{FpToFpExpr.class, Fp64("12.0"), ToFp(RNE, Fp16("12.0"), 11, 53)},
				{FpToFpExpr.class, Fp16("12.0"), ToFp(RNE, Fp32("12.0"), 5, 11)},
				{FpFromBvExpr.class, Fp16("0"), FromBv(RNE, BvUtils.bigIntegerToUnsignedBvLitExpr(BigInteger.ZERO, 16), FpType(5, 11), false)},
				{FpFromBvExpr.class, Fp16("1"), FromBv(RNE, BvUtils.bigIntegerToUnsignedBvLitExpr(BigInteger.ONE, 16), FpType(5, 11), false)},
				{FpFromBvExpr.class, Fp16("10"), FromBv(RNE, BvUtils.bigIntegerToUnsignedBvLitExpr(BigInteger.TEN, 16), FpType(5, 11), false)},
				{FpFromBvExpr.class, Fp16("0"), FromBv(RNE, BvUtils.bigIntegerToSignedBvLitExpr(BigInteger.ZERO, 16), FpType(5, 11), true)},
				{FpFromBvExpr.class, Fp16("1"), FromBv(RNE, BvUtils.bigIntegerToSignedBvLitExpr(BigInteger.ONE, 16), FpType(5, 11), true)},
				{FpFromBvExpr.class, Fp16("10"), FromBv(RNE, BvUtils.bigIntegerToSignedBvLitExpr(BigInteger.TEN, 16), FpType(5, 11), true)},
				{FpFromBvExpr.class, Fp16("0"), FromBv(RNE, BvUtils.bigIntegerToSignedBvLitExpr(BigInteger.ZERO.negate(), 16), FpType(5, 11), true)},
				{FpFromBvExpr.class, Fp16("-1"), FromBv(RNE, BvUtils.bigIntegerToSignedBvLitExpr(BigInteger.ONE.negate(), 16), FpType(5, 11), true)},
				{FpFromBvExpr.class, Fp16("-10"), FromBv(RNE, BvUtils.bigIntegerToSignedBvLitExpr(BigInteger.TEN.negate(), 16), FpType(5, 11), true)},
		});
	}

	private static Collection<?> LinuxSpecificTests() {
		if (!OsHelper.getOs().equals(OsHelper.OperatingSystem.LINUX)) return ImmutableSet.of();
		return Arrays.asList(new Object[][]{
				{FpRoundToIntegralExpr.class, Fp16("2.0"), RoundToIntegral(RNE, Fp16("1.5"))},
		});
	}

	private static Collection<?> WindowsSpecificTests() {
		if (!OsHelper.getOs().equals(OsHelper.OperatingSystem.WINDOWS)) return ImmutableSet.of();
		//noinspection RedundantArrayCreation
		return Arrays.asList(new Object[][]{
				// This is a placeholder for any tests that might be Windows-only
		});
	}

	private static Collection<?> NaNOperations() {
		return Arrays.asList(new Object[][]{
				{FpAddExpr.class, Fp16NaN(), Add(RNE, List.of(Fp16NaN(), Fp16("3.4")))},
				{FpSubExpr.class, Fp16NaN(), Sub(RNE, Fp16("5.5"), Fp16NaN())},
				{FpPosExpr.class, Fp16NaN(), Pos(Fp16NaN())},
				{FpNegExpr.class, Fp16NaN(), Neg(Fp16NaN())},
				{FpMulExpr.class, Fp16NaN(), Mul(RNE, List.of(Fp16NaN(), Fp16("3.4")))},
				{FpDivExpr.class, Fp16NaN(), Div(RNE, Fp16("7.14"), Fp16NaN())},
				{FpLeqExpr.class, Bool(false), Leq(Fp16("7.14"), Fp16NaN())},
				{FpGeqExpr.class, Bool(false), Geq(Fp16("7.14"), Fp16NaN())},
				{FpGtExpr.class, Bool(false), Gt(Fp16("7.14"), Fp16NaN())},
				{FpLtExpr.class, Bool(false), Lt(Fp16("7.14"), Fp16NaN())},
				{FpLeqExpr.class, Bool(false), Leq(Fp16NaN(), Fp16NaN())},
				{FpGeqExpr.class, Bool(false), Geq(Fp16NaN(), Fp16NaN())},
				{FpGtExpr.class, Bool(false), Gt(Fp16NaN(), Fp16NaN())},
				{FpLtExpr.class, Bool(false), Lt(Fp16NaN(), Fp16NaN())},
		});
	}

	private static Collection<?> InfinityOperations() {
		return Arrays.asList(new Object[][]{
				{FpAddExpr.class, Fp16PInf(), Add(RNA, List.of(Fp16PInf(), Fp16("3.4")))},
				{FpSubExpr.class, Fp16NInf(), Sub(RNA, Fp16("5.5"), Fp16PInf())},
				{FpPosExpr.class, Fp16PInf(), Pos(Fp16PInf())},
				{FpNegExpr.class, Fp16NInf(), Neg(Fp16PInf())},
				{FpMulExpr.class, Fp16PInf(), Mul(RNA, List.of(Fp16PInf(), Fp16("3.4")))},
				{FpDivExpr.class, Fp16("0"), Div(RNA, Fp16("7.14"), Fp16PInf())},
		});
	}

	private static FpLitExpr Fp16(final String lit) {
		return FpUtils.bigFloatToFpLitExpr(new BigFloat(lit, BINARY16), FpType(5, 11));
	}

	private static FpLitExpr Fp32(final String lit) {
		return FpUtils.bigFloatToFpLitExpr(new BigFloat(lit, BINARY32), FpType(8, 24));
	}

	private static FpLitExpr Fp64(final String lit) {
		return FpUtils.bigFloatToFpLitExpr(new BigFloat(lit, BINARY64), FpType(11, 53));
	}

	private static FpLitExpr Fp16NaN() {
		return FpUtils.bigFloatToFpLitExpr(BigFloat.NaN(BINARY16.precision), FpType(5, 11));
	}

	private static FpLitExpr Fp16PInf() {
		return FpUtils.bigFloatToFpLitExpr(BigFloat.positiveInfinity(BINARY16.precision), FpType(5, 11));
	}

	private static FpLitExpr Fp16NInf() {
		return FpUtils.bigFloatToFpLitExpr(BigFloat.negativeInfinity(BINARY16.precision), FpType(5, 11));
	}
}
