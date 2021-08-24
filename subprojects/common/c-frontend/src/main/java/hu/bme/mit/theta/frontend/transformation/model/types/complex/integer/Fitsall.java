package hu.bme.mit.theta.frontend.transformation.model.types.complex.integer;

import hu.bme.mit.theta.frontend.transformation.model.types.simple.CSimpleType;

public class Fitsall extends CInteger implements Unsigned {
	private static final int RANK = 100;
	public Fitsall(CSimpleType origin) {
		super(origin);
		rank = RANK;
		unsigned = false;
	}

	public <T, R> R accept(CComplexTypeVisitor<T, R> visitor, T param) {
		return visitor.visit(this, param);
	}


	@Override
	public String getTypeName() {
		return "fitsall";
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
