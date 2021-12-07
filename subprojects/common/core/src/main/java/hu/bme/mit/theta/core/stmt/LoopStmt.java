package hu.bme.mit.theta.core.stmt;

import hu.bme.mit.theta.common.Utils;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.inttype.IntType;

public final class LoopStmt implements Stmt {

	private final Stmt stmt;
	private final VarDecl<IntType> loopVariable;
	private final Expr<IntType> from;
	private final Expr<IntType> to;

	private static final int HASH_SEED = 361;
	private static final String STMT_LABEL = "loop";

	private volatile int hashCode = 0;

	private LoopStmt(final Stmt stmt, final VarDecl<IntType> loopVariable, final Expr<IntType> from, final Expr<IntType> to) {
		this.stmt = stmt;
		this.loopVariable = loopVariable;
		this.from = from;
		this.to = to;
	}

	public static LoopStmt of(final Stmt stmt, final VarDecl<IntType> loopVariable, final Expr<IntType> from, final Expr<IntType> to) {
		return new LoopStmt(stmt, loopVariable, from, to);
	}

	public Stmt getStmt() {
		return stmt;
	}

	public VarDecl<IntType> getLoopVariable() {
		return loopVariable;
	}

	public Expr<IntType> getFrom() {
		return from;
	}

	public Expr<IntType> getTo() {
		return to;
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
			result = 37 * result + stmt.hashCode() + loopVariable.hashCode() + from.hashCode() + to.hashCode();
			hashCode = result;
		}
		return result;
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		} else if (obj instanceof LoopStmt) {
			final LoopStmt that = (LoopStmt) obj;
			return this.getStmt().equals(that.getStmt())
					&& this.loopVariable.equals(that.loopVariable)
					&& this.from.equals(that.from)
					&& this.to.equals(that.to);
		} else {
			return false;
		}
	}

	@Override
	public String toString() {
		return Utils.lispStringBuilder(STMT_LABEL).add(loopVariable+" from "+from+" to "+to+" "+stmt).toString();
	}

}
