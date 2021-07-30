package hu.bme.mit.theta.xcfa.transformation.model.types.complex.integer.cshort;

import hu.bme.mit.theta.xcfa.transformation.model.types.complex.integer.CInteger;
import hu.bme.mit.theta.xcfa.transformation.model.types.simple.CSimpleType;

public abstract class CShort extends CInteger {
	protected CShort(CSimpleType origin) {
		super(origin);
	}
	public <T, R> R accept(CComplexTypeVisitor<T, R> visitor, T param) {
		return visitor.visit(this, param);
	}
}
