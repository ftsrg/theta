package hu.bme.mit.theta.xcfa.transformation.model.types.complex.visitors.bitvector;

import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.fptype.FpType;
import hu.bme.mit.theta.core.utils.BvUtils;
import hu.bme.mit.theta.core.utils.FpUtils;
import hu.bme.mit.theta.xcfa.transformation.ArchitectureConfig;
import hu.bme.mit.theta.xcfa.transformation.model.types.complex.CComplexType;
import hu.bme.mit.theta.xcfa.transformation.model.types.complex.integer.CInteger;
import hu.bme.mit.theta.xcfa.transformation.model.types.complex.integer.Signed;
import hu.bme.mit.theta.xcfa.transformation.model.types.complex.real.CDouble;
import hu.bme.mit.theta.xcfa.transformation.model.types.complex.real.CFloat;
import hu.bme.mit.theta.xcfa.transformation.model.types.complex.real.CLongDouble;
import org.kframework.mpfr.BigFloat;
import org.kframework.mpfr.BinaryMathContext;

import java.math.BigInteger;

public class UnitValueVisitor extends CComplexType.CComplexTypeVisitor<Void, Expr<?>> {
	public static final UnitValueVisitor instance = new UnitValueVisitor();

	@Override
	public Expr<?> visit(CDouble type, Void param) {
		return FpUtils.bigFloatToFpLitExpr(
				new BigFloat(
						"1.0",
						new BinaryMathContext(
								ArchitectureConfig.architecture.getBitWidth("double_s"),
								ArchitectureConfig.architecture.getBitWidth("double_e"))),
				FpType.of(
						ArchitectureConfig.architecture.getBitWidth("double_s"),
						ArchitectureConfig.architecture.getBitWidth("double_e")));
	}

	@Override
	public Expr<?> visit(CFloat type, Void param) {
		return FpUtils.bigFloatToFpLitExpr(
				new BigFloat(
						"1.0",
						new BinaryMathContext(
								ArchitectureConfig.architecture.getBitWidth("float_s"),
								ArchitectureConfig.architecture.getBitWidth("float_e"))),
				FpType.of(
						ArchitectureConfig.architecture.getBitWidth("float_s"),
						ArchitectureConfig.architecture.getBitWidth("float_e")));
	}

	@Override
	public Expr<?> visit(CLongDouble type, Void param) {
		return FpUtils.bigFloatToFpLitExpr(
				new BigFloat(
						"1.0",
						new BinaryMathContext(
								ArchitectureConfig.architecture.getBitWidth("longdouble_s"),
								ArchitectureConfig.architecture.getBitWidth("longdouble_e"))),
				FpType.of(
						ArchitectureConfig.architecture.getBitWidth("longdouble_s"),
						ArchitectureConfig.architecture.getBitWidth("longdouble_e")));
	}

	@Override
	public Expr<?> visit(CInteger type, Void param) {
		if(type instanceof Signed) {
			return BvUtils.bigIntegerToSignedBvLitExpr(BigInteger.ONE, type.width());
		} else {
			return BvUtils.bigIntegerToUnsignedBvLitExpr(BigInteger.ONE, type.width());
		}
	}
}
