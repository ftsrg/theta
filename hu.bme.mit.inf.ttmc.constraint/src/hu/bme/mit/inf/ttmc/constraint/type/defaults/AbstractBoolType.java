package hu.bme.mit.inf.ttmc.constraint.type.defaults;

import hu.bme.mit.inf.ttmc.constraint.type.BoolType;

public abstract class AbstractBoolType extends AbstractBaseType implements BoolType {

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
