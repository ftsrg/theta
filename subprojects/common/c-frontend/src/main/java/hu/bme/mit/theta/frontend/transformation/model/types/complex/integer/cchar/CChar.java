package hu.bme.mit.theta.frontend.transformation.model.types.complex.integer.cchar;

import hu.bme.mit.theta.frontend.transformation.model.types.complex.integer.CInteger;
import hu.bme.mit.theta.frontend.transformation.model.types.simple.CSimpleType;

public abstract class CChar extends CInteger {
	private static final int RANK = 10;
	protected CChar(CSimpleType origin) {
		super(origin);
		rank = RANK;
	}
	public <T, R> R accept(CComplexTypeVisitor<T, R> visitor, T param) {
		return visitor.visit(this, param);
	}

	@Override
	public String getTypeName() {
		return "char";
	}

	@Override
	public CInteger getSignedVersion() {
		return new CSignedChar(null);
	}
	@Override
	public CInteger getUnsignedVersion() {
		return new CUnsignedChar(null);
	}

}
