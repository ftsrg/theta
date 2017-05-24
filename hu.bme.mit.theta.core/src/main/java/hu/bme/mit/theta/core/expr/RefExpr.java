package hu.bme.mit.theta.core.expr;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.theta.core.decl.Decl;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.utils.ExprVisitor;

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
	public <P, R> R accept(final ExprVisitor<? super P, ? extends R> visitor, final P param) {
		return visitor.visit(this, param);
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
