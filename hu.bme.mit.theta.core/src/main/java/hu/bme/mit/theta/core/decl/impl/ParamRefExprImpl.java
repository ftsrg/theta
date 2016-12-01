package hu.bme.mit.theta.core.decl.impl;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.theta.core.decl.ParamDecl;
import hu.bme.mit.theta.core.expr.ParamRefExpr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.utils.ExprVisitor;

final class ParamRefExprImpl<DeclType extends Type> implements ParamRefExpr<DeclType> {

	private static final int HASH_SEED = 919;

	private volatile int hashCode = 0;

	private final ParamDecl<DeclType> paramDecl;

	ParamRefExprImpl(final ParamDecl<DeclType> paramDecl) {
		this.paramDecl = checkNotNull(paramDecl);
	}

	@Override
	public ParamDecl<DeclType> getDecl() {
		return paramDecl;
	}

	@Override
	public DeclType getType() {
		return paramDecl.getType();
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
			result = 31 * result + paramDecl.hashCode();
			hashCode = result;
		}
		return result;
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		} else if (obj instanceof ParamRefExpr<?>) {
			final ParamRefExpr<?> that = (ParamRefExpr<?>) obj;
			return this.getDecl().equals(that.getDecl());
		} else {
			return false;
		}
	}

	@Override
	public String toString() {
		return paramDecl.getName();
	}

}
