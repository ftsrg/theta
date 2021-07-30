package hu.bme.mit.theta.xcfa.transformation.model.types.complex.integer.clonglong;

import hu.bme.mit.theta.xcfa.transformation.model.types.simple.CSimpleType;

public class CUnsignedLongLong extends CLongLong {
	public CUnsignedLongLong(CSimpleType origin) {
		super(origin);
		unsigned = true;
	}
	public <T, R> R accept(CComplexTypeVisitor<T, R> visitor, T param) {
		return visitor.visit(this, param);
	}
}
