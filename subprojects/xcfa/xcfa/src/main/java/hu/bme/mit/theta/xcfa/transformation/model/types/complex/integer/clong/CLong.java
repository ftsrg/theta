package hu.bme.mit.theta.xcfa.transformation.model.types.complex.integer.clong;

import hu.bme.mit.theta.xcfa.transformation.model.types.complex.integer.CInteger;
import hu.bme.mit.theta.xcfa.transformation.model.types.simple.CSimpleType;

public abstract class CLong extends CInteger {
	protected CLong(CSimpleType origin) {
		super(origin);
	}
	public <T, R> R accept(CComplexTypeVisitor<T, R> visitor, T param) {
		return visitor.visit(this, param);
	}
}
