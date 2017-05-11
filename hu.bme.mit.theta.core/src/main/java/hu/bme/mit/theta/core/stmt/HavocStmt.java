package hu.bme.mit.theta.core.stmt;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.theta.common.ObjectUtils;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.utils.StmtVisitor;

public final class HavocStmt<DeclType extends Type> implements Stmt {

	private static final int HASH_SEED = 929;
	private volatile int hashCode = 0;

	private final VarDecl<DeclType> varDecl;

	HavocStmt(final VarDecl<DeclType> varDecl) {
		this.varDecl = checkNotNull(varDecl);
	}

	public VarDecl<DeclType> getVarDecl() {
		return varDecl;
	}

	@Override
	public <P, R> R accept(final StmtVisitor<? super P, ? extends R> visitor, final P param) {
		return visitor.visit(this, param);
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
		return ObjectUtils.toStringBuilder("Havoc").add(varDecl.getName()).toString();
	}
}
