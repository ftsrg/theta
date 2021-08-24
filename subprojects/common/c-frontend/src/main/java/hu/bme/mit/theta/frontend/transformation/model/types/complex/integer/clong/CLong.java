package hu.bme.mit.theta.frontend.transformation.model.types.complex.integer.clong;

import hu.bme.mit.theta.frontend.transformation.model.types.complex.integer.CInteger;
import hu.bme.mit.theta.frontend.transformation.model.types.simple.CSimpleType;

public abstract class CLong extends CInteger {
	private static final int RANK = 40;
	protected CLong(CSimpleType origin) {
		super(origin);
		rank = RANK;
	}
	public <T, R> R accept(CComplexTypeVisitor<T, R> visitor, T param) {
		return visitor.visit(this, param);
	}


	@Override
	public String getTypeName() {
		return "long";
	}

	@Override
	public CInteger getSignedVersion() {
		return new CSignedLong(null);
	}
	@Override
	public CInteger getUnsignedVersion() {
		return new CUnsignedLong(null);
	}
}
