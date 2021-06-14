package hu.bme.mit.theta.xcfa.transformation.c.types;

import static com.google.common.base.Preconditions.checkState;

/**
 * This type either represents a built-in type like int or float, or a typedef'd named type.
 */
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
		switch(namedType) {
			case "long":
				if(cType.isLong()) {
					cType.setLongLong(true);
					cType.setLong(false);
				} else {
					cType.setLong(true);
				}
				break;
			case "short":
				setShort(true);
				break;
			default:
				if(!cType.isTypedef()) throw new RuntimeException("namedType should be short or long or type specifier, instead it is " + namedType);
				break;
		}
	}

	@Override
	public CType getBaseType() {
		NamedType namedType = new NamedType(getNamedType());
		namedType.setAtomic(this.isAtomic());
		namedType.setExtern(this.isExtern());
		namedType.setTypedef(this.isTypedef());
		namedType.setVolatile(this.isVolatile());
		namedType.setSigned(this.isSigned());
		namedType.setShort(this.isShort());
		namedType.setLong(this.isLong());
		namedType.setLongLong(this.isLongLong());

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
		if(isShort()) stringBuilder.append("short ");
		if(isLong()) stringBuilder.append("long ");
		if(isLongLong()) stringBuilder.append("long long ");

		stringBuilder.append(namedType);
		return stringBuilder.toString();
	}

	@Override
	public boolean isVoid() {
		return namedType.equals("void") && getPointerLevel() == 0;
	}

	@Override
	public CType copyOf() {
		CType namedType = new NamedType(getNamedType());
		namedType.setAtomic(this.isAtomic());
		namedType.setExtern(this.isExtern());
		namedType.setTypedef(this.isTypedef());
		namedType.setVolatile(this.isVolatile());
		namedType.setSigned(this.isSigned());
		namedType.setShort(this.isShort());
		namedType.setLong(this.isLong());
		namedType.setLongLong(this.isLongLong());
		for(int i = 0; i < this.getPointerLevel(); i++) {
			namedType.incrementPointer();
		}

		return namedType;
	}
}

