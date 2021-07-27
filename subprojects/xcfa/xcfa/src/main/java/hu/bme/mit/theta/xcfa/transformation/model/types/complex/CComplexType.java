package hu.bme.mit.theta.xcfa.transformation.model.types.complex;

import hu.bme.mit.theta.xcfa.transformation.model.types.simple.CSimpleType;

public abstract class CComplexType {
	private final CSimpleType origin;

	protected CComplexType(CSimpleType origin) {
		this.origin = origin;
	}

	public CSimpleType getOrigin() {
		return origin;
	}
}
