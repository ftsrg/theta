package hu.bme.mit.theta.frontend.transformation.model.types.complex.integer.cshort;

import hu.bme.mit.theta.frontend.transformation.model.types.complex.integer.CInteger;
import hu.bme.mit.theta.frontend.transformation.model.types.simple.CSimpleType;

public abstract class CShort extends CInteger {
	private static final int RANK = 20;
	protected CShort(CSimpleType origin) {
		super(origin);
		rank = RANK;
	}
	public <T, R> R accept(CComplexTypeVisitor<T, R> visitor, T param) {
		return visitor.visit(this, param);
	}

	@Override
	public String getTypeName() {
		return "short";
	}

	@Override
	public CInteger getSignedVersion() {
		return new CSignedShort(null);
	}
	@Override
	public CInteger getUnsignedVersion() {
		return new CUnsignedShort(null);
	}
}
