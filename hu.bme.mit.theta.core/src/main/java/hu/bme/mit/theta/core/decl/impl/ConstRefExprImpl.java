package hu.bme.mit.theta.core.decl.impl;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.theta.core.decl.ConstDecl;
import hu.bme.mit.theta.core.expr.ConstRefExpr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.utils.ExprVisitor;

final class ConstRefExprImpl<DeclType extends Type> extends ConstRefExpr<DeclType> {

	private static final int HASH_SEED = 167;
	private volatile int hashCode = 0;

	private final ConstDecl<DeclType> constDecl;

	ConstRefExprImpl(final ConstDecl<DeclType> constDecl) {
		this.constDecl = checkNotNull(constDecl);
	}

	@Override
	public ConstDecl<DeclType> getDecl() {
		return constDecl;
	}

	@Override
	public DeclType getType() {
		return constDecl.getType();
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
			result = 31 * result + constDecl.hashCode();
			hashCode = result;
		}
		return result;
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		} else if (obj instanceof ConstRefExpr<?>) {
			final ConstRefExpr<?> that = (ConstRefExpr<?>) obj;
			return this.getDecl().equals(that.getDecl());
		} else {
			return false;
		}
	}

	@Override
	public String toString() {
		return constDecl.getName();
	}

}
