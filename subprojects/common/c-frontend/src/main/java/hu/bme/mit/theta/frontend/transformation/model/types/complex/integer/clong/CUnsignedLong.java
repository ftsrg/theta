package hu.bme.mit.theta.frontend.transformation.model.types.complex.integer.clong;

import hu.bme.mit.theta.frontend.transformation.model.types.complex.integer.Unsigned;
import hu.bme.mit.theta.frontend.transformation.model.types.simple.CSimpleType;

public class CUnsignedLong extends CLong implements Unsigned {
	public CUnsignedLong(CSimpleType origin) {
		super(origin);
		unsigned = true;
	}

	public <T, R> R accept(CComplexTypeVisitor<T, R> visitor, T param) {
		return visitor.visit(this, param);
	}
}
