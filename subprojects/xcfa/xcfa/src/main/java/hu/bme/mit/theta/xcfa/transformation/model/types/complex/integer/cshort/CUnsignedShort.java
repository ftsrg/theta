package hu.bme.mit.theta.xcfa.transformation.model.types.complex.integer.cshort;

import hu.bme.mit.theta.xcfa.transformation.model.types.simple.CSimpleType;

public class CUnsignedShort extends CShort {
	public CUnsignedShort(CSimpleType origin) {
		super(origin);
	}
	public <T, R> R accept(CComplexTypeVisitor<T, R> visitor, T param) {
		return visitor.visit(this, param);
	}
}
