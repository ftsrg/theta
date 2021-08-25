package hu.bme.mit.theta.frontend.transformation.model.types.complex.integer.clonglong;

import hu.bme.mit.theta.frontend.transformation.model.types.complex.integer.CInteger;
import hu.bme.mit.theta.frontend.transformation.model.types.simple.CSimpleType;

public abstract class CLongLong extends CInteger {
	private static final int RANK = 50;
	protected CLongLong(CSimpleType origin) {
		super(origin);
		rank = RANK;
	}
	public <T, R> R accept(CComplexTypeVisitor<T, R> visitor, T param) {
		return visitor.visit(this, param);
	}
	@Override
	public String getTypeName() {
		return "longlong";
	}
	@Override
	public CInteger getSignedVersion() {
		return new CSignedLongLong(null);
	}
	@Override
	public CInteger getUnsignedVersion() {
		return new CUnsignedLongLong(null);
	}
}
