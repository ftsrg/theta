package hu.bme.mit.theta.xcfa.transformation.model.types.complex.compound;

import hu.bme.mit.theta.xcfa.transformation.model.types.simple.CSimpleType;

public class CStruct extends CCompound {
	protected CStruct(CSimpleType origin) {
		super(origin);
	}

	public <T, R> R accept(CComplexTypeVisitor<T, R> visitor, T param) {
		return visitor.visit(this, param);
	}
}
