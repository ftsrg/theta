package hu.bme.mit.theta.xcfa.transformation.model.types.complex.integer;

import hu.bme.mit.theta.xcfa.transformation.model.types.complex.CComplexType;
import hu.bme.mit.theta.xcfa.transformation.model.types.simple.CSimpleType;

public abstract class CInteger extends CComplexType {
	protected CInteger(CSimpleType origin) {
		super(origin);
	}
	public <T, R> R accept(CComplexTypeVisitor<T, R> visitor, T param) {
		return visitor.visit(this, param);
	}
}
