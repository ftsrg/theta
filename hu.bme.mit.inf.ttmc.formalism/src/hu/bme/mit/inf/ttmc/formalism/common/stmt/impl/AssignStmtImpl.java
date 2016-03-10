package hu.bme.mit.inf.ttmc.formalism.common.stmt.impl;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.type.Type;
import hu.bme.mit.inf.ttmc.formalism.common.decl.VarDecl;
import hu.bme.mit.inf.ttmc.formalism.common.stmt.AssignStmt;

public final class AssignStmtImpl<DeclType extends Type, ExprType extends DeclType> extends AbstractStmt implements AssignStmt<DeclType, ExprType> {

	private final static int HASHSEED = 409;
	private volatile int hashCode = 0;
	
	private final VarDecl<DeclType> varDecl;
	private final Expr<ExprType> expr;
	
	public AssignStmtImpl(final VarDecl<DeclType> varDecl, final Expr<ExprType> expr) {
		this.varDecl = checkNotNull(varDecl);
		this.expr = checkNotNull(expr);
	}
	
	@Override
	public VarDecl<DeclType> getVarDecl() {
		return varDecl;
	}

	@Override
	public Expr<ExprType> getExpr() {
		return expr;
	}
	
	@Override
	public int hashCode() {
		if (hashCode == 0) {
			hashCode = HASHSEED;
			hashCode = 37 * hashCode + varDecl.hashCode();
			hashCode = 37 * hashCode + expr.hashCode();
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
			final AssignStmtImpl<?, ?> that = (AssignStmtImpl<?, ?>) obj;
			return this.varDecl.equals(that.varDecl) && this.expr.equals(that.expr);
		} else {
			return false;
		}
	}

	@Override
	public String toString() {
		final StringBuilder sb = new StringBuilder();
		sb.append("Assign");
		sb.append("(");
		sb.append(varDecl.getName());
		sb.append(", ");
		sb.append(expr);
		sb.append(")");
		return sb.toString();
	}
}
