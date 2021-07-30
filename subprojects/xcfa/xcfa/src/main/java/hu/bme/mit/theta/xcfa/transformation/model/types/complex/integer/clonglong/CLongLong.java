package hu.bme.mit.theta.xcfa.transformation.model.types.complex.integer.clonglong;

import hu.bme.mit.theta.xcfa.transformation.model.types.complex.integer.CInteger;
import hu.bme.mit.theta.xcfa.transformation.model.types.simple.CSimpleType;

public abstract class CLongLong extends CInteger {
	protected CLongLong(CSimpleType origin) {
		super(origin);
	}
	public <T, R> R accept(CComplexTypeVisitor<T, R> visitor, T param) {
		return visitor.visit(this, param);
	}
}
