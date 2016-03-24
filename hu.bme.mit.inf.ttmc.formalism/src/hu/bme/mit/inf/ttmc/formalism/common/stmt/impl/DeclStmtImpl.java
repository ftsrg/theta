package hu.bme.mit.inf.ttmc.formalism.common.stmt.impl;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.inf.ttmc.constraint.type.Type;
import hu.bme.mit.inf.ttmc.formalism.common.decl.VarDecl;
import hu.bme.mit.inf.ttmc.formalism.common.stmt.DeclStmt;

public final class DeclStmtImpl<DeclType extends Type> implements DeclStmt<DeclType> {

	private static final int HASH_SEED = 4201;

	private volatile int hashCode = 0;

	private final VarDecl<DeclType> varDecl;

	public DeclStmtImpl(final VarDecl<DeclType> varDecl) {
		this.varDecl = checkNotNull(varDecl);
	}

	@Override
	public VarDecl<DeclType> getVarDecl() {
		return varDecl;
	}

	@Override
	public int hashCode() {
		int result = hashCode;
		if (result == 0) {
			result = HASH_SEED;
			result = 37 * result + varDecl.hashCode();
			hashCode = result;
		}
		return result;
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		} else if (obj instanceof DeclStmt<?>) {
			final DeclStmt<?> that = (DeclStmt<?>) obj;
			return this.getVarDecl().equals(that.getVarDecl());
		} else {
			return false;
		}
	}

	@Override
	public String toString() {
		final StringBuilder sb = new StringBuilder();
		sb.append("Decl");
		sb.append("(");
		sb.append(varDecl);
		sb.append(")");
		return sb.toString();
	}

}
