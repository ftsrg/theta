package hu.bme.mit.theta.xcfa.transformation.model.types.simple;

import hu.bme.mit.theta.xcfa.transformation.model.types.complex.CComplexType;
import hu.bme.mit.theta.xcfa.transformation.model.types.complex.CVoid;
import hu.bme.mit.theta.xcfa.transformation.model.types.complex.integer.cbool.CBool;
import hu.bme.mit.theta.xcfa.transformation.model.types.complex.integer.cchar.CSignedChar;
import hu.bme.mit.theta.xcfa.transformation.model.types.complex.integer.cchar.CUnsignedChar;
import hu.bme.mit.theta.xcfa.transformation.model.types.complex.integer.cint.CSignedInt;
import hu.bme.mit.theta.xcfa.transformation.model.types.complex.integer.cint.CUnsignedInt;
import hu.bme.mit.theta.xcfa.transformation.model.types.complex.integer.clong.CSignedLong;
import hu.bme.mit.theta.xcfa.transformation.model.types.complex.integer.clong.CUnsignedLong;
import hu.bme.mit.theta.xcfa.transformation.model.types.complex.integer.clonglong.CSignedLongLong;
import hu.bme.mit.theta.xcfa.transformation.model.types.complex.integer.clonglong.CUnsignedLongLong;
import hu.bme.mit.theta.xcfa.transformation.model.types.complex.integer.cshort.CSignedShort;
import hu.bme.mit.theta.xcfa.transformation.model.types.complex.integer.cshort.CUnsignedShort;
import hu.bme.mit.theta.xcfa.transformation.model.types.complex.real.CDouble;
import hu.bme.mit.theta.xcfa.transformation.model.types.complex.real.CFloat;
import hu.bme.mit.theta.xcfa.transformation.model.types.complex.real.CLongDouble;

/**
 * This type either represents a built-in type like int or float, or a typedef'd named type.
 */
public class NamedType extends CSimpleType {
	private final String namedType;

	NamedType(final String namedType){
		this.namedType = namedType;
	}

	@Override
	public CComplexType getActualType() {
		switch (namedType) {
			case "char": if(isSigned()) return new CSignedChar(this); else return new CUnsignedChar(this);
			case "int": if(isBool()) return new CBool(this);
						else if(isSigned()) {
							if(isLong()) return new CSignedLong(this);
							else if(isLongLong()) return new CSignedLongLong(this);
							else if(isShort()) return new CSignedShort(this);
							else return new CSignedInt(this);
						} else {
							if(isLong()) return new CUnsignedLong(this);
							else if(isLongLong()) return new CUnsignedLongLong(this);
							else if(isShort()) return new CUnsignedShort(this);
							else return new CUnsignedInt(this);
						}
			case "double": if(isLong()) return new CLongDouble(this); else return new CDouble(this);
			case "float": return new CFloat(this);
			case "void": return new CVoid(this);
			default: throw new UnsupportedOperationException("Unknown simple type " + namedType);
		}
	}

	public static NamedType getIntType() {
		NamedType namedType = new NamedType("int");
		namedType.setSigned(true);
		return namedType;
	}

	public static NamedType getUnsignedIntType() {
		NamedType namedType = new NamedType("int");
		namedType.setSigned(false);
		return namedType;
	}

	public static NamedType getBoolType() {
		NamedType namedType = new NamedType("_Bool");
		namedType.setSigned(false);
		return namedType;
	}

	public String getNamedType() {
		return namedType;
	}

	@Override
	protected void patch(CSimpleType cSimpleType) {
		switch(namedType) {
			case "long":
				if(cSimpleType.isLong()) {
					cSimpleType.setLongLong(true);
					cSimpleType.setLong(false);
				} else {
					cSimpleType.setLong(true);
				}
				break;
			case "short":
				cSimpleType.setShort(true);
				break;
			case "_Bool":
				cSimpleType.setBool(true);
				break;
			default:
				if(!cSimpleType.isTypedef()) throw new RuntimeException("namedType should be short or long or type specifier, instead it is " + namedType);
				break;
		}
	}

	@Override
	public CSimpleType getBaseType() {
		NamedType namedType = new NamedType(getNamedType());
		namedType.setAtomic(this.isAtomic());
		namedType.setExtern(this.isExtern());
		namedType.setTypedef(this.isTypedef());
		namedType.setVolatile(this.isVolatile());
		namedType.setSigned(this.isSigned());
		namedType.setShort(this.isShort());
		namedType.setBool(this.isBool());
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
		if(isBool()) stringBuilder.append("_Bool ");
		if(isLongLong()) stringBuilder.append("long long ");

		stringBuilder.append(namedType);
		return stringBuilder.toString();
	}

	@Override
	public boolean isVoid() {
		return namedType.equals("void") && getPointerLevel() == 0;
	}

	@Override
	public CSimpleType copyOf() {
		CSimpleType namedType = new NamedType(getNamedType());
		namedType.setAtomic(this.isAtomic());
		namedType.setExtern(this.isExtern());
		namedType.setTypedef(this.isTypedef());
		namedType.setVolatile(this.isVolatile());
		namedType.setSigned(this.isSigned());
		namedType.setShort(this.isShort());
		namedType.setLong(this.isLong());
		namedType.setBool(this.isBool());
		namedType.setLongLong(this.isLongLong());
		for(int i = 0; i < this.getPointerLevel(); i++) {
			namedType.incrementPointer();
		}

		return namedType;
	}
}

