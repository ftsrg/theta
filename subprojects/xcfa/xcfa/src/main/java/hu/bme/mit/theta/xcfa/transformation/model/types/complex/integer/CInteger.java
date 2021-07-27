package hu.bme.mit.theta.xcfa.transformation.model.types.complex.integer;

import hu.bme.mit.theta.xcfa.transformation.model.types.complex.CComplexType;
import hu.bme.mit.theta.xcfa.transformation.model.types.simple.CSimpleType;

public abstract class CInteger extends CComplexType {
	protected CInteger(CSimpleType origin) {
		super(origin);
	}
}
