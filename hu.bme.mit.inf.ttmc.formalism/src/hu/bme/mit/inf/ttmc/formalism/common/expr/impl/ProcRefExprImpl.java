package hu.bme.mit.inf.ttmc.formalism.common.expr.impl;

import hu.bme.mit.inf.ttmc.constraint.type.Type;
import hu.bme.mit.inf.ttmc.constraint.utils.ExprVisitor;
import hu.bme.mit.inf.ttmc.formalism.common.decl.ProcDecl;
import hu.bme.mit.inf.ttmc.formalism.common.expr.ProcRefExpr;
import hu.bme.mit.inf.ttmc.formalism.common.expr.visitor.ProcRefExprVisitor;

public class ProcRefExprImpl<ReturnType extends Type> implements ProcRefExpr<ReturnType> {

	private final static int HASHCODE = 1229;
	private volatile int hashCode = 0;
	
	private final ProcDecl<ReturnType> procDecl;
	
	
	public ProcRefExprImpl(final ProcDecl<ReturnType> procDecl) {
		this.procDecl = procDecl;
	}
	
	@Override
	public ProcDecl<ReturnType> getDecl() {
		return procDecl;
	}
	
	@Override
	public int hashCode() {
		if (hashCode == 0) {
			hashCode = HASHCODE;
			hashCode = 31 * hashCode + procDecl.hashCode();
		}

		return hashCode;
	}
	
	@Override
	public boolean equals(Object obj) {
		if (this == obj) {
			return true;
		} else if (obj == null) {
			return false;
		} else if (this.getClass() == obj.getClass()) {
			final ProcRefExprImpl<?> that = (ProcRefExprImpl<?>) obj;
			return this.procDecl.equals(that.procDecl);
		} else {
			return false;
		}
	}

	@Override
	public final String toString() {
		return getDecl().getName();
	}

	@Override
	public <P, R> R accept(ExprVisitor<? super P, ? extends R> visitor, P param) {
		if (visitor instanceof ProcRefExprVisitor<?, ?>) {
			final ProcRefExprVisitor<? super P, ? extends R> sVisitor = (ProcRefExprVisitor<? super P, ? extends R>) visitor;
			return sVisitor.visit(this, param);
		} else {
			throw new UnsupportedOperationException();
		}
	}
}
