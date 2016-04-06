package hu.bme.mit.inf.ttmc.formalism.common.stmt.impl;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.inf.ttmc.constraint.type.Type;
import hu.bme.mit.inf.ttmc.formalism.common.decl.VarDecl;
import hu.bme.mit.inf.ttmc.formalism.common.stmt.HavocStmt;

public final class HavocStmtImpl<DeclType extends Type> extends AbstractStmt implements HavocStmt<DeclType> {

	private static final int HASH_SEED = 929;
	private volatile int hashCode = 0;

	private final VarDecl<DeclType> varDecl;

	public HavocStmtImpl(final VarDecl<DeclType> varDecl) {
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
			result = 31 * result + varDecl.hashCode();
			hashCode = result;
		}
		return result;
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		} else if (obj instanceof HavocStmt<?>) {
			final HavocStmt<?> that = (HavocStmt<?>) obj;
			return this.getVarDecl().equals(that.getVarDecl());
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
