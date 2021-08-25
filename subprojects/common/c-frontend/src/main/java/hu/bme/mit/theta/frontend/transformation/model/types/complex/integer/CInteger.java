package hu.bme.mit.theta.frontend.transformation.model.types.complex.integer;

import hu.bme.mit.theta.frontend.transformation.model.types.complex.CComplexType;
import hu.bme.mit.theta.frontend.transformation.model.types.simple.CSimpleType;

public abstract class CInteger extends CComplexType {
	protected int rank;
	protected boolean unsigned = false;
	protected CInteger(CSimpleType origin) {
		super(origin);
	}
	public <T, R> R accept(CComplexTypeVisitor<T, R> visitor, T param) {
		return visitor.visit(this, param);
	}

	@Override
	public CComplexType getSmallestCommonType(CComplexType type) {
		if(type instanceof CInteger && ((CInteger) type).rank <= rank) {
			if(((CInteger) type).unsigned) {
				if(unsigned || type.width() < width()) {
					return this;
				} else {
					return getUnsignedVersion();
				}
			} else {
				return this;
			}
		} else {
			return type.getSmallestCommonType(this);
		}
	}


	public abstract CInteger getSignedVersion();

	public abstract CInteger getUnsignedVersion();
}
