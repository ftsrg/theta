package hu.bme.mit.theta.core.type.anytype;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.theta.core.Decl;
import hu.bme.mit.theta.core.LitExpr;
import hu.bme.mit.theta.core.NullaryExpr;
import hu.bme.mit.theta.core.Type;
import hu.bme.mit.theta.core.model.Assignment;

public final class RefExpr<DeclType extends Type> extends NullaryExpr<DeclType> {

	private static final int HASH_SEED = 167;
	private volatile int hashCode = 0;

	private final Decl<DeclType> decl;

	RefExpr(final Decl<DeclType> decl) {
		this.decl = checkNotNull(decl);
	}

	public Decl<DeclType> getDecl() {
		return decl;
	}

	@Override
	public DeclType getType() {
		return decl.getType();
	}

	@Override
	public LitExpr<DeclType> eval(final Assignment assignment) {
		return (LitExpr<DeclType>) assignment.eval(decl).get();
	}

	@Override
	public int hashCode() {
		int result = hashCode;
		if (result == 0) {
			result = HASH_SEED;
			result = 31 * result + decl.hashCode();
			hashCode = result;
		}
		return result;
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		} else if (obj instanceof RefExpr) {
			final RefExpr<?> that = (RefExpr<?>) obj;
			return this.getDecl().equals(that.getDecl());
		} else {
			return false;
		}
	}

	@Override
	public String toString() {
		return decl.getName();
	}

}
