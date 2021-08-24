package hu.bme.mit.theta.frontend.transformation.model.types.complex.integer.cchar;

import hu.bme.mit.theta.frontend.transformation.model.types.complex.integer.Unsigned;
import hu.bme.mit.theta.frontend.transformation.model.types.simple.CSimpleType;

public class CUnsignedChar extends CChar implements Unsigned {
	public CUnsignedChar(CSimpleType origin) {
		super(origin);
		unsigned = true;
	}
	public <T, R> R accept(CComplexTypeVisitor<T, R> visitor, T param) {
		return visitor.visit(this, param);
	}
}
