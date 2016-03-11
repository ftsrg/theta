package hu.bme.mit.inf.ttmc.constraint.type.defaults;

import hu.bme.mit.inf.ttmc.constraint.type.BaseType;

public abstract class AbstractBaseType extends AbstractType implements BaseType {

	@Override
	public boolean equals(final Object obj) {
		if (obj == null) {
			return false;
		} else {
			return (this.getClass() == obj.getClass());
		}
	}
	
}
