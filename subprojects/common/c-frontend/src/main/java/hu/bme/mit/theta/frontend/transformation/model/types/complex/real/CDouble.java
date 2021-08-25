package hu.bme.mit.theta.frontend.transformation.model.types.complex.real;

import hu.bme.mit.theta.frontend.transformation.model.types.simple.CSimpleType;

public class CDouble extends CReal {
	private static final int RANK = 10;
	public CDouble(CSimpleType origin) {
		super(origin);
		rank = RANK;
	}

	public <T, R> R accept(CComplexTypeVisitor<T, R> visitor, T param) {
		return visitor.visit(this, param);
	}
}
