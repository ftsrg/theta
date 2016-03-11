package hu.bme.mit.inf.ttmc.constraint.type.defaults;

import hu.bme.mit.inf.ttmc.constraint.type.IntType;

public abstract class AbstractIntType extends AbstractBaseType implements IntType {
	
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
