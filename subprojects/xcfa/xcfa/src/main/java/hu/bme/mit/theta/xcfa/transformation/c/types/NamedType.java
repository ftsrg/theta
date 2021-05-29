package hu.bme.mit.theta.xcfa.transformation.c.types;

import static com.google.common.base.Preconditions.checkState;

public class NamedType extends CType{
	private final String namedType;
	NamedType(final String namedType){
		this.namedType = namedType;
	}

	public String getNamedType() {
		return namedType;
	}

	@Override
	protected void patch(CType cType) {
		checkState(cType.getAssociatedName() == null, "Associated name already set!");
		cType.setAssociatedName(namedType);
	}
}
