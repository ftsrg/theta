package hu.bme.mit.theta.xcfa.transformation.model.types.complex.integer.cint;

import hu.bme.mit.theta.xcfa.transformation.model.types.simple.CSimpleType;

public class CSignedInt extends CInt {
	public CSignedInt(CSimpleType origin) {
		super(origin);
	}
	public <T, R> R accept(CComplexTypeVisitor<T, R> visitor, T param) {
		return visitor.visit(this, param);
	}
}
