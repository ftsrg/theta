package hu.bme.mit.theta.xcfa.transformation.model.types.complex;

import hu.bme.mit.theta.xcfa.transformation.model.types.simple.CSimpleType;

public class CVoid extends CComplexType{

	public CVoid(CSimpleType origin) {
		super(origin);
	}

	public <T, R> R accept(CComplexTypeVisitor<T, R> visitor, T param) {
		return visitor.visit(this, param);
	}
}
