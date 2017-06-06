package hu.bme.mit.theta.core.decl;

import static hu.bme.mit.theta.core.type.anytype.Exprs.Ref;

import hu.bme.mit.theta.core.Type;
import hu.bme.mit.theta.core.type.anytype.RefExpr;

public abstract class Decl<DeclType extends Type> {
	private static final int HASH_SEED = 5351;
	private volatile int hashCode = 0;

	private final RefExpr<DeclType> ref;

	public Decl() {
		this.ref = Ref(this);
	}

	public RefExpr<DeclType> getRef() {
		return ref;
	}

	@Override
	public final int hashCode() {
		int result = hashCode;
		if (result == 0) {
			result = HASH_SEED;
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

	public abstract String getName();

	public abstract DeclType getType();

}
