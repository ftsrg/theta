package hu.bme.mit.theta.xcfa.transformation.c.types;

import java.util.List;

public abstract class CType {
	private int pointerLevel = 0;
	private boolean atomic = false;
	private boolean extern = false;
	private boolean typedef = false;
	private boolean isVolatile = false;
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
}
