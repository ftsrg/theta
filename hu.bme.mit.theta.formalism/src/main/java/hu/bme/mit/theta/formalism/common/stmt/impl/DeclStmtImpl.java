package hu.bme.mit.theta.formalism.common.stmt.impl;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Optional;

import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.formalism.common.decl.VarDecl;
import hu.bme.mit.theta.formalism.common.stmt.DeclStmt;

final class DeclStmtImpl<DeclType extends Type, ExprType extends DeclType> extends AbstractStmt
		implements DeclStmt<DeclType, ExprType> {

	private static final int HASH_SEED = 4201;

	private volatile int hashCode = 0;

	private final VarDecl<DeclType> varDecl;

	private final Optional<Expr<ExprType>> initVal;

	DeclStmtImpl(final VarDecl<DeclType> varDecl) {
		this.varDecl = checkNotNull(varDecl);
		initVal = Optional.empty();
	}

	public DeclStmtImpl(final VarDecl<DeclType> varDecl, final Expr<ExprType> initVal) {
		this.varDecl = checkNotNull(varDecl);
		this.initVal = Optional.of(checkNotNull(initVal));
	}

	@Override
	public VarDecl<DeclType> getVarDecl() {
		return varDecl;
	}

	@Override
	public Optional<Expr<ExprType>> getInitVal() {
		return initVal;
	}

	@Override
	public int hashCode() {
		int result = hashCode;
		if (result == 0) {
			result = HASH_SEED;
			result = 31 * result + varDecl.hashCode();
			result = 31 * result + initVal.hashCode();
			hashCode = result;
		}
		return result;
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		} else if (obj instanceof DeclStmt<?, ?>) {
			final DeclStmt<?, ?> that = (DeclStmt<?, ?>) obj;
			return this.getVarDecl().equals(that.getVarDecl()) && this.getInitVal().equals(that.getInitVal());
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
		if (initVal.isPresent()) {
			sb.append(", ");
			sb.append(initVal.get());
		}
		sb.append(")");
		return sb.toString();
	}

}
