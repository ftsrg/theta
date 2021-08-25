package hu.bme.mit.theta.frontend.transformation.model.types.complex.real;

import hu.bme.mit.theta.frontend.transformation.model.types.simple.CSimpleType;

public class CLongDouble extends CReal {
	private static final int RANK = 20;
	public CLongDouble(CSimpleType origin) {
		super(origin);
		rank = RANK;
	}

	public <T, R> R accept(CComplexTypeVisitor<T, R> visitor, T param) {
		return visitor.visit(this, param);
	}
}
