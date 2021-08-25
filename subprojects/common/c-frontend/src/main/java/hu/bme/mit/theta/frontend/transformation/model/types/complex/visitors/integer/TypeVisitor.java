package hu.bme.mit.theta.frontend.transformation.model.types.complex.visitors.integer;

import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.arraytype.ArrayType;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CComplexType;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CVoid;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.compound.CArray;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.compound.CStruct;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.integer.CInteger;

import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;

public class TypeVisitor extends CComplexType.CComplexTypeVisitor<Void, Type> {
	public static final TypeVisitor instance = new TypeVisitor();

	@Override
	public Type visit(CInteger type, Void param) {
		return Int();
	}

	@Override
	public Type visit(CVoid type, Void param) {
		return Int();
	}

	@Override
	public Type visit(CArray type, Void param) {
		return ArrayType.of(Int(), type.getEmbeddedType().getSmtType());
	}

	@Override
	public Type visit(CStruct type, Void param) {
		return Bool();
	}
}
