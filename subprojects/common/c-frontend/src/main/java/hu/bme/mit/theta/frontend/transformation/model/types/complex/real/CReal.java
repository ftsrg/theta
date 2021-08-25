package hu.bme.mit.theta.frontend.transformation.model.types.complex.real;

import hu.bme.mit.theta.frontend.transformation.model.types.complex.CComplexType;
import hu.bme.mit.theta.frontend.transformation.model.types.simple.CSimpleType;

public abstract class CReal extends CComplexType {
	protected int rank;
	protected CReal(CSimpleType origin) {
		super(origin);
	}

	public <T, R> R accept(CComplexTypeVisitor<T, R> visitor, T param) {
		return visitor.visit(this, param);
	}

	@Override
	public CComplexType getSmallestCommonType(CComplexType type) {
		if(!(type instanceof CReal) || ((CReal) type).rank <= rank) return this;
		else return type.getSmallestCommonType(this);
	}
}
