package hu.bme.mit.inf.ttmc.program.expr.impl;

import hu.bme.mit.inf.ttmc.constraint.type.Type;
import hu.bme.mit.inf.ttmc.program.decl.VarDecl;
import hu.bme.mit.inf.ttmc.program.expr.VarRefExpr;

public final class VarRefExprImpl<DeclType extends Type> implements VarRefExpr<DeclType> {

	private final static int HASHCODE = 313;
	private volatile int hashCode = 0;
	
	private final VarDecl<DeclType> varDecl;
	
	
	public VarRefExprImpl(final VarDecl<DeclType> varDecl) {
		this.varDecl = varDecl;
	}
	
	@Override
	public VarDecl<DeclType> getDecl() {
		return varDecl;
	}

	@Override
	public int hashCode() {
		if (hashCode == 0) {
			hashCode = HASHCODE;
			hashCode = 31 * hashCode + varDecl.hashCode();
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
			final VarRefExprImpl<?> that = (VarRefExprImpl<?>) obj;
			return this.varDecl.equals(that.varDecl);
		} else {
			return false;
		}
	}

	@Override
	public final String toString() {
		return getDecl().getName();
	}

}
