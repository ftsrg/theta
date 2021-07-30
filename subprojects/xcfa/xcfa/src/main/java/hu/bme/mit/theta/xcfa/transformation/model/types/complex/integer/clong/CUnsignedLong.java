package hu.bme.mit.theta.xcfa.transformation.model.types.complex.integer.clong;

import hu.bme.mit.theta.xcfa.transformation.model.types.simple.CSimpleType;

public class CUnsignedLong extends CLong {
	public CUnsignedLong(CSimpleType origin) {
		super(origin);
		unsigned = true;
	}

	public <T, R> R accept(CComplexTypeVisitor<T, R> visitor, T param) {
		return visitor.visit(this, param);
	}
}
