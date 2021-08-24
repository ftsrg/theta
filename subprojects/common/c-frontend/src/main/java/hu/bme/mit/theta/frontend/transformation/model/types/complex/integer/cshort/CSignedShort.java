package hu.bme.mit.theta.frontend.transformation.model.types.complex.integer.cshort;

import hu.bme.mit.theta.frontend.transformation.model.types.complex.integer.Signed;
import hu.bme.mit.theta.frontend.transformation.model.types.simple.CSimpleType;

public class CSignedShort extends CShort implements Signed {
	public CSignedShort(CSimpleType origin) {
		super(origin);
	}
	public <T, R> R accept(CComplexTypeVisitor<T, R> visitor, T param) {
		return visitor.visit(this, param);
	}
}
