package hu.bme.mit.theta.frontend.transformation.model.types.complex.visitors.bitvector;

import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.arraytype.ArrayType;
import hu.bme.mit.theta.core.type.bvtype.BvType;
import hu.bme.mit.theta.core.type.fptype.FpType;
import hu.bme.mit.theta.frontend.transformation.ArchitectureConfig;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CComplexType;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CVoid;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.compound.CArray;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.compound.CStruct;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.integer.CInteger;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.integer.Signed;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.real.CDouble;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.real.CFloat;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.real.CLongDouble;

import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool;

public class TypeVisitor extends CComplexType.CComplexTypeVisitor<Void, Type> {
	public static final TypeVisitor instance = new TypeVisitor();

	@Override
	public Type visit(CDouble type, Void param) {
		return FpType.of(
						ArchitectureConfig.architecture.getBitWidth("double_e"),
						ArchitectureConfig.architecture.getBitWidth("double_s"));
	}

	@Override
	public Type visit(CFloat type, Void param) {
		return FpType.of(
				ArchitectureConfig.architecture.getBitWidth("float_e"),
				ArchitectureConfig.architecture.getBitWidth("float_s"));
	}

	@Override
	public Type visit(CLongDouble type, Void param) {
		return FpType.of(
				ArchitectureConfig.architecture.getBitWidth("longdouble_e"),
				ArchitectureConfig.architecture.getBitWidth("longdouble_s"));
	}

	@Override
	public Type visit(CArray type, Void param) {
		return ArrayType.of(CComplexType.getUnsignedLong().getSmtType(), type.getEmbeddedType().getSmtType());
	}

	@Override
	public Type visit(CInteger type, Void param) {
		return BvType.of(type.width(), type instanceof Signed);
	}

	@Override
	public Type visit(CVoid type, Void param) {
		return BvType.of(1, false);
	}

	@Override
	public Type visit(CStruct type, Void param) {
		return Bool();
	}
}
