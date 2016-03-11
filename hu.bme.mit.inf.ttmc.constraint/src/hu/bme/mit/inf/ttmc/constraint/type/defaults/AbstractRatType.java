package hu.bme.mit.inf.ttmc.constraint.type.defaults;

import hu.bme.mit.inf.ttmc.constraint.type.RatType;

public abstract class AbstractRatType extends AbstractBaseType implements RatType {
	
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
