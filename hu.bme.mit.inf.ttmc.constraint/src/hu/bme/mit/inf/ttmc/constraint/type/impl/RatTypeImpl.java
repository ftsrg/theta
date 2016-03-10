package hu.bme.mit.inf.ttmc.constraint.type.impl;

import hu.bme.mit.inf.ttmc.constraint.type.RatType;

public class RatTypeImpl extends AbstractBaseType implements RatType {
	
	private static final String TYPENAME = "Rat";

	@Override
	public int hashCode() {
		return 385863;
	}

	@Override
	public String toString() {
		return TYPENAME;
	}

}
