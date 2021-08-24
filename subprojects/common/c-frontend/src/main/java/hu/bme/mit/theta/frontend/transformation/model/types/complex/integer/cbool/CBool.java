package hu.bme.mit.theta.frontend.transformation.model.types.complex.integer.cbool;

import hu.bme.mit.theta.frontend.transformation.model.types.complex.integer.CInteger;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.integer.Unsigned;
import hu.bme.mit.theta.frontend.transformation.model.types.simple.CSimpleType;

public class CBool extends CInteger implements Unsigned {
	private static final int RANK = 0;
	public CBool(CSimpleType origin) {
		super(origin);
		rank = RANK;
		unsigned = true;
	}

	public <T, R> R accept(CComplexTypeVisitor<T, R> visitor, T param) {
		return visitor.visit(this, param);
	}


	@Override
	public String getTypeName() {
		return "bool";
	}

	@Override
	public CInteger getSignedVersion() {
		throw new RuntimeException("Bool does not have a signed version!");
	}
	@Override
	public CInteger getUnsignedVersion() {
		return this;
	}
}
