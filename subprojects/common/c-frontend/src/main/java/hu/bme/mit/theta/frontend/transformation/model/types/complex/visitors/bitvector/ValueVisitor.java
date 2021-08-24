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

public class ValueVisitor extends CComplexType.CComplexTypeVisitor<String, LitExpr<?>> {
	public static final ValueVisitor instance = new ValueVisitor();

	@Override
	public LitExpr<?> visit(CDouble type, String param) {
		return FpUtils.bigFloatToFpLitExpr(
				new BigFloat(
						param,
						new BinaryMathContext(
								ArchitectureConfig.architecture.getBitWidth("double_e"),
								ArchitectureConfig.architecture.getBitWidth("double_s"))),
				FpType.of(
						ArchitectureConfig.architecture.getBitWidth("double_e"),
						ArchitectureConfig.architecture.getBitWidth("double_s")));
	}

	@Override
	public LitExpr<?> visit(CFloat type, String param) {
		return FpUtils.bigFloatToFpLitExpr(
				new BigFloat(
						param,
						new BinaryMathContext(
								ArchitectureConfig.architecture.getBitWidth("float_e"),
								ArchitectureConfig.architecture.getBitWidth("float_s"))),
				FpType.of(
						ArchitectureConfig.architecture.getBitWidth("float_e"),
						ArchitectureConfig.architecture.getBitWidth("float_s")));
	}

	@Override
	public LitExpr<?> visit(CLongDouble type, String param) {
		return FpUtils.bigFloatToFpLitExpr(
				new BigFloat(
						param,
						new BinaryMathContext(
								ArchitectureConfig.architecture.getBitWidth("longdouble_e"),
								ArchitectureConfig.architecture.getBitWidth("longdouble_s"))),
				FpType.of(
						ArchitectureConfig.architecture.getBitWidth("longdouble_e"),
						ArchitectureConfig.architecture.getBitWidth("longdouble_s")));
	}

	@Override
	public LitExpr<?> visit(CInteger type, String param) {
		if(type instanceof Signed) {
			return BvUtils.bigIntegerToSignedBvLitExpr(new BigInteger(param), type.width());
		} else {
			return BvUtils.bigIntegerToUnsignedBvLitExpr(new BigInteger(param), type.width());
		}
	}

	@Override
	public LitExpr<?> visit(CArray type, String param) {
		return getExpr(type, param);
	}

	private <IndexType extends Type, ElemType extends Type> ArrayLitExpr<IndexType, ElemType> getExpr(CArray type, String param) {
		//noinspection unchecked
		ArrayType<IndexType, ElemType> smtType = (ArrayType<IndexType, ElemType>) type.getSmtType();
		return Array(List.of(), cast(type.getEmbeddedType().getValue(param), smtType.getElemType()), smtType);
	}
}
