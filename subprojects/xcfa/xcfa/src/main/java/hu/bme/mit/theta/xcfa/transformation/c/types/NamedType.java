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

	@Override
	public CType getBaseType() {
		NamedType namedType = new NamedType(getNamedType());
		namedType.setAtomic(this.isAtomic());
		namedType.setExtern(this.isExtern());
		namedType.setTypedef(this.isTypedef());
		namedType.setVolatile(this.isVolatile());
		return namedType;
	}

	@Override
	public String toString() {
		StringBuilder stringBuilder = new StringBuilder();
		if(isTypedef()) stringBuilder.append("typedef ");
		if(isExtern()) stringBuilder.append("extern ");
		if(isVolatile()) stringBuilder.append("volatile ");
		if(isAtomic()) stringBuilder.append("_Atomic ");
		if(!isSigned()) stringBuilder.append("unsigned ");
		stringBuilder.append(namedType);
		return stringBuilder.toString();
	}

	@Override
	public boolean isVoid() {
		return namedType.equals("void") && getPointerLevel() == 0;
	}
}
