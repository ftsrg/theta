package hu.bme.mit.theta.core.stmt;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.theta.common.ObjectUtils;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.utils.StmtVisitor;

public final class AssignStmt<DeclType extends Type> implements Stmt {

	private static final int HASH_SEED = 409;
	private volatile int hashCode = 0;

	private final VarDecl<DeclType> varDecl;
	private final Expr<DeclType> expr;

	AssignStmt(final VarDecl<DeclType> varDecl, final Expr<DeclType> expr) {
		this.varDecl = checkNotNull(varDecl);
		this.expr = checkNotNull(expr);
	}

	public VarDecl<DeclType> getVarDecl() {
		return varDecl;
	}

	public Expr<DeclType> getExpr() {
		return expr;
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
			result = 31 * result + expr.hashCode();
			hashCode = result;
		}
		return result;
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		} else if (obj instanceof AssignStmt) {
			final AssignStmt<?> that = (AssignStmt<?>) obj;
			return this.getVarDecl().equals(that.getVarDecl()) && this.getExpr().equals(that.getExpr());
		} else {
			return false;
		}
	}

	@Override
	public String toString() {
		return ObjectUtils.toStringBuilder("Assign").add(varDecl.getName()).add(expr).toString();
	}
}
