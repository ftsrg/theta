package hu.bme.mit.theta.frontend.transformation.model.types.complex.compound;

import hu.bme.mit.theta.frontend.transformation.model.types.complex.CComplexType;
import hu.bme.mit.theta.frontend.transformation.model.types.simple.CSimpleType;

public class CArray extends CCompound {
	private final CComplexType embeddedType;

	public CArray(CSimpleType origin, CComplexType embeddedType) {
		super(origin);
		this.embeddedType = embeddedType;
	}

	public CComplexType getEmbeddedType() {
		return embeddedType;
	}

	public <T, R> R accept(CComplexTypeVisitor<T, R> visitor, T param) {
		return visitor.visit(this, param);
	}

}
