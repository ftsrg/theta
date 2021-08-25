package hu.bme.mit.theta.frontend.transformation.model.types.complex.compound;

import hu.bme.mit.theta.frontend.transformation.model.types.complex.CComplexType;
import hu.bme.mit.theta.frontend.transformation.model.types.simple.CSimpleType;

public class CPointer extends CCompound {
	private final CComplexType embeddedType;

	public CPointer(CSimpleType origin, CComplexType embeddedType) {
		super(origin);
		this.embeddedType = embeddedType;
	}

	public <T, R> R accept(CComplexTypeVisitor<T, R> visitor, T param) {
		return visitor.visit(this, param);
	}

	public CComplexType getEmbeddedType() {
		return embeddedType;
	}
}
