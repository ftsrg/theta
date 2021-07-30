package hu.bme.mit.theta.xcfa.transformation.model.types.complex.integer.cchar;

import hu.bme.mit.theta.xcfa.transformation.model.types.simple.CSimpleType;

public class CUnsignedChar extends CChar {
	public CUnsignedChar(CSimpleType origin) {
		super(origin);
	}
	public <T, R> R accept(CComplexTypeVisitor<T, R> visitor, T param) {
		return visitor.visit(this, param);
	}
}
