package hu.bme.mit.theta.core.decl.impl;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.theta.common.ObjectUtils;
import hu.bme.mit.theta.core.decl.Decl;
import hu.bme.mit.theta.core.type.Type;

public abstract class AbstractDecl<DeclType extends Type> implements Decl<DeclType> {

	private final String name;
	private final DeclType type;

	private volatile int hashCode = 0;

	protected AbstractDecl(final String name, final DeclType type) {
		checkNotNull(name);
		checkNotNull(type);
		checkArgument(name.length() > 0);
		this.name = name;
		this.type = type;
	}

	@Override
	public final String getName() {
		return name;
	}

	@Override
	public final DeclType getType() {
		return type;
	}

	@Override
	public final int hashCode() {
		int result = hashCode;
		if (result == 0) {
			result = getHashSeed();
			result = 31 * result + getName().hashCode();
			result = 31 * result + getType().hashCode();
			hashCode = result;
		}
		return result;
	}

	@Override
	public final boolean equals(final Object obj) {
		return this == obj;
	}

	@Override
	public final String toString() {
		return ObjectUtils.toStringBuilder(getDeclLabel()).add(getName()).add(getType()).toString();
	}

	protected abstract int getHashSeed();

	protected abstract String getDeclLabel();

}
