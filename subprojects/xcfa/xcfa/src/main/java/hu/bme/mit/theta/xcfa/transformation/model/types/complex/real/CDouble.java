package hu.bme.mit.theta.xcfa.transformation.model.types.complex.real;

import hu.bme.mit.theta.xcfa.transformation.model.types.simple.CSimpleType;

public class CDouble extends CReal {
	public CDouble(CSimpleType origin) {
		super(origin);
	}

	public <T, R> R accept(CComplexTypeVisitor<T, R> visitor, T param) {
		return visitor.visit(this, param);
	}
}
