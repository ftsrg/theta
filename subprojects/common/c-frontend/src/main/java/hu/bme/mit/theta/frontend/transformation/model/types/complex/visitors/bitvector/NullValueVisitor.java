package hu.bme.mit.theta.frontend.transformation.model.types.complex.visitors.bitvector;

import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.arraytype.ArrayLitExpr;
import hu.bme.mit.theta.core.type.arraytype.ArrayType;
import hu.bme.mit.theta.core.type.fptype.FpType;
import hu.bme.mit.theta.core.utils.BvUtils;
import hu.bme.mit.theta.core.utils.FpUtils;
import hu.bme.mit.theta.frontend.transformation.ArchitectureConfig;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CComplexType;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.compound.CArray;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.integer.CInteger;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.integer.Signed;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.real.CDouble;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.real.CFloat;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.real.CLongDouble;
import org.kframework.mpfr.BigFloat;
import org.kframework.mpfr.BinaryMathContext;

import java.math.BigInteger;
import java.util.List;

import static hu.bme.mit.theta.core.type.arraytype.ArrayExprs.Array;
import static hu.bme.mit.theta.core.utils.TypeUtils.cast;

public class NullValueVisitor extends CComplexType.CComplexTypeVisitor<Void, LitExpr<?>> {
	public static final NullValueVisitor instance = new NullValueVisitor();

	@Override
	public LitExpr<?> visit(CDouble type, Void param) {
		return FpUtils.bigFloatToFpLitExpr(
				new BigFloat(
						"0.0",
						new BinaryMathContext(
								ArchitectureConfig.architecture.getBitWidth("double_e"),
								ArchitectureConfig.architecture.getBitWidth("double_s"))),
				FpType.of(
						ArchitectureConfig.architecture.getBitWidth("double_e"),
						ArchitectureConfig.architecture.getBitWidth("double_s")));
	}

	@Override
	public LitExpr<?> visit(CFloat type, Void param) {
		return FpUtils.bigFloatToFpLitExpr(
				new BigFloat(
						"0.0",
						new BinaryMathContext(
								ArchitectureConfig.architecture.getBitWidth("float_e"),
								ArchitectureConfig.architecture.getBitWidth("float_s"))),
				FpType.of(
						ArchitectureConfig.architecture.getBitWidth("float_e"),
						ArchitectureConfig.architecture.getBitWidth("float_s")));
	}

	@Override
	public LitExpr<?> visit(CLongDouble type, Void param) {
		return FpUtils.bigFloatToFpLitExpr(
				new BigFloat(
						"0.0",
						new BinaryMathContext(
								ArchitectureConfig.architecture.getBitWidth("longdouble_e"),
								ArchitectureConfig.architecture.getBitWidth("longdouble_s"))),
				FpType.of(
						ArchitectureConfig.architecture.getBitWidth("longdouble_e"),
						ArchitectureConfig.architecture.getBitWidth("longdouble_s")));
	}

	@Override
	public LitExpr<?> visit(CInteger type, Void param) {
		if(type instanceof Signed) {
			return BvUtils.bigIntegerToSignedBvLitExpr(BigInteger.ZERO, type.width());
		} else {
			return BvUtils.bigIntegerToUnsignedBvLitExpr(BigInteger.ZERO, type.width());
		}
	}

	@Override
	public LitExpr<?> visit(CArray type, Void param) {
		return getExpr(type);
	}

	private <IndexType extends Type, ElemType extends Type> ArrayLitExpr<IndexType, ElemType> getExpr(CArray type) {
		//noinspection unchecked
		ArrayType<IndexType, ElemType> smtType = (ArrayType<IndexType, ElemType>) type.getSmtType();
		return Array(List.of(), cast(type.getEmbeddedType().getNullValue(), smtType.getElemType()), smtType);
	}
}
