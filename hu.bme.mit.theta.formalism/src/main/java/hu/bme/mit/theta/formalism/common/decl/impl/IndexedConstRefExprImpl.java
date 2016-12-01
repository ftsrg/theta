package hu.bme.mit.theta.formalism.common.decl.impl;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.theta.core.decl.IndexedConstDecl;
import hu.bme.mit.theta.core.expr.ConstRefExpr;
import hu.bme.mit.theta.core.expr.IndexedConstRefExpr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.utils.ExprVisitor;

final class IndexedConstRefExprImpl<DeclType extends Type> implements IndexedConstRefExpr<DeclType> {

	// same as for AbstractDecl
	private static final int HASH_SEED = 167;

	private final IndexedConstDecl<DeclType> decl;

	private volatile int hashCode = 0;

	IndexedConstRefExprImpl(final IndexedConstDecl<DeclType> constDecl) {
		this.decl = checkNotNull(constDecl);
	}

	@Override
	public IndexedConstDecl<DeclType> getDecl() {
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
			// not a bug - symmetry of equals() is more obvious this way
		} else if (obj instanceof ConstRefExpr<?>) {
			final ConstRefExpr<?> that = (ConstRefExpr<?>) obj;
			return this.getDecl().equals(that.getDecl());
		} else {
			return false;
		}
	}

	@Override
	public String toString() {
		final StringBuilder sb = new StringBuilder();
		sb.append(decl.getName());
		sb.append(":");
		sb.append(decl.getIndex());
		return sb.toString();
	}

}
