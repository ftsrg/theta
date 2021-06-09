package hu.bme.mit.theta.xcfa.transformation.c.types;

import java.util.List;

/**
 * Any received CType instance will either be a NamedType or an Enum (and later a Struct, still under development).
 * The other subclasses are helper classes to provide metadata on the signedness, atomicity, etc. of the type.
 */
public abstract class CType {
	private int pointerLevel = 0;
	private boolean signed = true;
	private boolean atomic = false;
	private boolean extern = false;
	private boolean typedef = false;
	private boolean isVolatile = false;
	private boolean isShort = false;
	private boolean isLong = false;
	private boolean isLongLong = false;

	/**
	 * According to the grammar, the first declared variable is part of the type
	 * (e.g. `int a` will result in a named type `int`, with an associated name `a`)
	 */
	private String associatedName = null;

	public int getPointerLevel() {
		return pointerLevel;
	}

	public void incrementPointer(){
		++pointerLevel;
	}

	public CType apply(List<CType> newCtypes) {
		for (CType newCtype : newCtypes) {
			newCtype.patch(this);
		}
		return this;
	}

	protected abstract void patch(CType cType);

	public boolean isAtomic() {
		return atomic;
	}

	public void setAtomic(boolean atomic) {
		this.atomic = atomic;
	}

	public boolean isExtern() {
		return extern;
	}

	public void setExtern(boolean extern) {
		this.extern = extern;
	}

	public boolean isTypedef() {
		return typedef;
	}

	public void setTypedef(boolean typedef) {
		this.typedef = typedef;
	}

	public boolean isVolatile() {
		return isVolatile;
	}

	public void setVolatile(boolean aVolatile) {
		isVolatile = aVolatile;
	}

	public String getAssociatedName() {
		return associatedName;
	}

	public void setAssociatedName(String associatedName) {
		this.associatedName = associatedName;
	}

	/**
	 * Returns the base type of the C type e.g. `int* a` will result in a CType of int pointer
	 * but the semantic meaning is that it is an int and the declared variable is of pointer type
	 * (this is a shortcoming of the grammar)
	 * @return base type
	 */
	public CType getBaseType() {
		throw new UnsupportedOperationException("Not yet implemented!");
	}

	public boolean isSigned() {
		return signed;
	}

	public void setSigned(boolean signed) {
		this.signed = signed;
	}

	public boolean isVoid() {
		return false;
	}

	public boolean isLongLong() {
		return isLongLong;
	}

	public void setLongLong(boolean longLong) {
		isLongLong = longLong;
	}

	public boolean isLong() {
		return isLong;
	}

	public void setLong(boolean aLong) {
		isLong = aLong;
	}

	public boolean isShort() {
		return isShort;
	}

	public void setShort(boolean aShort) {
		isShort = aShort;
	}
}
