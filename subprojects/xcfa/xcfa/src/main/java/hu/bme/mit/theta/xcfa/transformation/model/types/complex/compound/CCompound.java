package hu.bme.mit.theta.xcfa.transformation.model.types.complex.compound;

import hu.bme.mit.theta.xcfa.transformation.model.types.complex.CComplexType;
import hu.bme.mit.theta.xcfa.transformation.model.types.simple.CSimpleType;

public abstract class CCompound extends CComplexType {
	protected CCompound(CSimpleType origin) {
		super(origin);
	}
}
