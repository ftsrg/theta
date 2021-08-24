package hu.bme.mit.theta.frontend.transformation.model.types.complex.integer.cint;

import hu.bme.mit.theta.frontend.transformation.model.types.complex.integer.Unsigned;
import hu.bme.mit.theta.frontend.transformation.model.types.simple.CSimpleType;

public class CUnsignedInt extends CInt implements Unsigned {
	public CUnsignedInt(CSimpleType origin) {
		super(origin);
		unsigned = true;
	}
	public <T, R> R accept(CComplexTypeVisitor<T, R> visitor, T param) {
		return visitor.visit(this, param);
	}
}
