package hu.bme.mit.inf.ttmc.formalism.stmt.impl;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.inf.ttmc.constraint.type.Type;
import hu.bme.mit.inf.ttmc.formalism.decl.VarDecl;
import hu.bme.mit.inf.ttmc.formalism.stmt.HavocStmt;

public class HavocStmtImpl<DeclType extends Type> extends AbstractStmt implements HavocStmt<DeclType> {

	private final static int HASHSEED = 929;
	private volatile int hashCode = 0;
	
	final VarDecl<DeclType> varDecl;
	
	public HavocStmtImpl(final VarDecl<DeclType> varDecl) {
		this.varDecl = checkNotNull(varDecl);
	}
	
	@Override
	public VarDecl<DeclType> getVarDecl() {
		return varDecl;
	}
	
	@Override
	public int hashCode() {
		if (hashCode == 0) {
			hashCode = HASHSEED;
			hashCode = 37 * hashCode + varDecl.hashCode();
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
			final HavocStmtImpl<?> that = (HavocStmtImpl<?>) obj;
			return this.varDecl.equals(that.varDecl);
		} else {
			return false;
		}
	}

	@Override
	public String toString() {
		final StringBuilder sb = new StringBuilder();
		sb.append("Havoc");
		sb.append("(");
		sb.append(varDecl.toString());
		sb.append(")");
		return sb.toString();
	}
}
