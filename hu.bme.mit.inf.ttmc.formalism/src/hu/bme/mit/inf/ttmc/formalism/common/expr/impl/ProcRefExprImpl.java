package hu.bme.mit.inf.ttmc.formalism.common.expr.impl;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.inf.ttmc.core.type.Type;
import hu.bme.mit.inf.ttmc.core.utils.ExprVisitor;
import hu.bme.mit.inf.ttmc.formalism.common.decl.ProcDecl;
import hu.bme.mit.inf.ttmc.formalism.common.expr.ProcRefExpr;
import hu.bme.mit.inf.ttmc.formalism.common.expr.visitor.ProcRefExprVisitor;
import hu.bme.mit.inf.ttmc.formalism.common.type.ProcType;

class ProcRefExprImpl<ReturnType extends Type> implements ProcRefExpr<ReturnType> {

	private final static int HASH_SEED = 1229;

	private final ProcDecl<ReturnType> procDecl;

	private volatile int hashCode = 0;

	ProcRefExprImpl(final ProcDecl<ReturnType> procDecl) {
		this.procDecl = checkNotNull(procDecl);
	}

	@Override
	public final ProcDecl<ReturnType> getDecl() {
		return procDecl;
	}

	@Override
	public final ProcType<ReturnType> getType() {
		return getDecl().getType();
	}

	@Override
	public final <P, R> R accept(final ExprVisitor<? super P, ? extends R> visitor, final P param) {
		if (visitor instanceof ProcRefExprVisitor<?, ?>) {
			final ProcRefExprVisitor<? super P, ? extends R> sVisitor = (ProcRefExprVisitor<? super P, ? extends R>) visitor;
			return sVisitor.visit(this, param);
		} else {
			throw new UnsupportedOperationException();
		}
	}

	@Override
	public final int hashCode() {
		int result = hashCode;
		if (result == 0) {
			result = HASH_SEED;
			result = 31 * result + procDecl.hashCode();
			hashCode = result;
		}
		return result;
	}

	@Override
	public final boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		} else if (obj instanceof ProcRefExpr<?>) {
			final ProcRefExpr<?> that = (ProcRefExpr<?>) obj;
			return this.getDecl().equals(that.getDecl());
		} else {
			return false;
		}
	}

	@Override
	public final String toString() {
		return getDecl().getName();
	}
}
