package hu.bme.mit.theta.xcfa.transformation.model.types.complex.integer.cint;

import hu.bme.mit.theta.xcfa.transformation.model.types.simple.CSimpleType;

public class CUnsignedInt extends CInt {
	public CUnsignedInt(CSimpleType origin) {
		super(origin);
		unsigned = true;
	}
	public <T, R> R accept(CComplexTypeVisitor<T, R> visitor, T param) {
		return visitor.visit(this, param);
	}
}
