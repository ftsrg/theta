package hu.bme.mit.theta.formalism.common.decl.impl;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.utils.ExprVisitor;
import hu.bme.mit.theta.formalism.common.decl.VarDecl;
import hu.bme.mit.theta.formalism.common.expr.VarRefExpr;
import hu.bme.mit.theta.formalism.common.expr.visitor.VarRefExprVisitor;

final class VarRefExprImpl<DeclType extends Type> implements VarRefExpr<DeclType> {

	private static final int HASH_SEED = 313;

	private volatile int hashCode = 0;

	private final VarDecl<DeclType> varDecl;

	VarRefExprImpl(final VarDecl<DeclType> varDecl) {
		this.varDecl = checkNotNull(varDecl);
	}

	@Override
	public VarDecl<DeclType> getDecl() {
		return varDecl;
	}

	@Override
	public DeclType getType() {
		return varDecl.getType();
	}

	@Override
	public final <P, R> R accept(final ExprVisitor<? super P, ? extends R> visitor, final P param) {
		if (visitor instanceof VarRefExprVisitor<?, ?>) {
			final VarRefExprVisitor<? super P, ? extends R> sVisitor = (VarRefExprVisitor<? super P, ? extends R>) visitor;
			return sVisitor.visit(this, param);
		} else {
			throw new UnsupportedOperationException();
		}
	}

	@Override
	public int hashCode() {
		int result = hashCode;
		if (result == 0) {
			result = HASH_SEED;
			result = 31 * result + varDecl.hashCode();
			hashCode = result;
		}
		return result;
	}

	@Override
	public final boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		} else if (obj instanceof VarRefExpr<?>) {
			final VarRefExpr<?> that = (VarRefExpr<?>) obj;
			return this.getDecl().equals(that.getDecl());
		} else {
			return false;
		}
	}

	@Override
	public String toString() {
		return varDecl.getName();
	}
}
