package hu.bme.mit.inf.ttmc.constraint.type.impl;

import hu.bme.mit.inf.ttmc.constraint.type.BoolType;

public class BoolTypeImpl extends AbstractBaseType implements BoolType {

	private static final String TYPENAME = "Bool";

	@Override
	public int hashCode() {
		return 754364;
	}

	@Override
	public String toString() {
		return TYPENAME;
	}

}
