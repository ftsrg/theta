package hu.bme.mit.theta.frontend.transformation.model.types.complex.integer.cint;

import hu.bme.mit.theta.frontend.transformation.model.types.complex.integer.CInteger;
import hu.bme.mit.theta.frontend.transformation.model.types.simple.CSimpleType;

public abstract class CInt extends CInteger {
	private static final int RANK = 30;
	protected CInt(CSimpleType origin) {
		super(origin);
		rank = RANK;
	}
	public <T, R> R accept(CComplexTypeVisitor<T, R> visitor, T param) {
		return visitor.visit(this, param);
	}


	@Override
	public String getTypeName() {
		return "int";
	}

	@Override
	public CInteger getSignedVersion() {
		return new CSignedInt(null);
	}
	@Override
	public CInteger getUnsignedVersion() {
		return new CUnsignedInt(null);
	}
}
