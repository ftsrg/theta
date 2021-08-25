package hu.bme.mit.theta.frontend.transformation.model.types.complex.integer.cchar;

import hu.bme.mit.theta.frontend.transformation.model.types.complex.integer.Signed;
import hu.bme.mit.theta.frontend.transformation.model.types.simple.CSimpleType;

public class CSignedChar extends CChar implements Signed {
	public CSignedChar(CSimpleType origin) {
		super(origin);
	}
	public <T, R> R accept(CComplexTypeVisitor<T, R> visitor, T param) {
		return visitor.visit(this, param);
	}
}
