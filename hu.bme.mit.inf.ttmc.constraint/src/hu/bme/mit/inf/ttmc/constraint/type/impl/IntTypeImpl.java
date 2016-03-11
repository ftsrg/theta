package hu.bme.mit.inf.ttmc.constraint.type.impl;

import hu.bme.mit.inf.ttmc.constraint.type.IntType;
import hu.bme.mit.inf.ttmc.constraint.type.defaults.AbstractBaseType;

public class IntTypeImpl extends AbstractBaseType implements IntType {
	
	private static final String TYPENAME = "Int";
	
	@Override
	public int hashCode() {
		return 222670;
	}
	
	@Override
	public String toString() {
		return TYPENAME;
	}
	
}
