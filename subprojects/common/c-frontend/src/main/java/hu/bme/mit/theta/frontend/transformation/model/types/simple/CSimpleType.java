package hu.bme.mit.theta.frontend.transformation.model.types.simple;

import hu.bme.mit.theta.frontend.transformation.model.types.complex.CComplexType;

import java.util.List;

/**
 * Any received CType instance will either be a NamedType or an Enum (and later a Struct, still under development).
 * The other subclasses are helper classes to provide metadata on the signedness, atomicity, etc. of the type.
 */
public abstract class CSimpleType {
	private int pointerLevel = 0;
	private Boolean signed = null;
	private boolean bool = false;
	private boolean atomic = false;
	private boolean extern = false;
	private boolean typedef = false;
	private boolean isVolatile = false;
	private boolean isShort = false;
	private boolean isLong = false;
	private boolean isLongLong = false;
	private boolean isThreadLocal = false;

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

	public CSimpleType apply(List<CSimpleType> newCtypes) {
		for (CSimpleType newCtype : newCtypes) {
			newCtype.patch(this);
		}
		return this;
	}

	protected abstract void patch(CSimpleType cSimpleType);

	public boolean isBool() {
		return bool;
	}

	public void setBool(boolean bool) {
		if(bool) setSigned(false); // _Bool isn't signed, but signed might be the default value in some cases
		this.bool = bool;
	}

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
	public CSimpleType getBaseType() {
		throw new UnsupportedOperationException("Not yet implemented!");
	}

	public Boolean isSigned() {
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

	public CSimpleType copyOf() {
		throw new UnsupportedOperationException("Abstract base class CSimpleType should not be copied");
	}

	public CComplexType getActualType() {
		throw new UnsupportedOperationException("Abstract base class CSimpleType should not be used");
	}

	protected void setThreadLocal(boolean threadLocal) {
		this.isThreadLocal = threadLocal;
	}

	public boolean isThreadLocal() {
		return isThreadLocal;
	}
}
