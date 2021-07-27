package hu.bme.mit.theta.xcfa.transformation.model.types.complex.real;

import hu.bme.mit.theta.xcfa.transformation.model.types.complex.CComplexType;
import hu.bme.mit.theta.xcfa.transformation.model.types.simple.CSimpleType;

public abstract class CReal extends CComplexType {
	protected CReal(CSimpleType origin) {
		super(origin);
	}
}
