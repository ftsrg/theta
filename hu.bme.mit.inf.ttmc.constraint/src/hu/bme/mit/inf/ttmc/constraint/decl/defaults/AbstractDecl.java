package hu.bme.mit.inf.ttmc.constraint.decl.defaults;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.inf.ttmc.constraint.decl.Decl;
import hu.bme.mit.inf.ttmc.constraint.type.Type;

public abstract class AbstractDecl<DeclType extends Type, DeclKind extends Decl<DeclType, DeclKind>>
		implements Decl<DeclType, DeclKind> {

	private final String name;
	private final DeclType type;

	private volatile int hashCode;

	protected AbstractDecl(final String name, final DeclType type) {
		checkNotNull(name);
		checkArgument(name.length() > 0);
		this.name = name;
		this.type = checkNotNull(type);
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
		final StringBuilder sb = new StringBuilder();
		sb.append(getDeclLabel());
		sb.append("(");
		sb.append(getName());
		sb.append(", ");
		sb.append(getType());
		sb.append(")");
		return sb.toString();
	}

	protected abstract int getHashSeed();

	protected abstract String getDeclLabel();

}
