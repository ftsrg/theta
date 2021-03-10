package hu.bme.mit.theta.core.stmt;

import hu.bme.mit.theta.common.Utils;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.inttype.IntType;

public final class LoopStmt implements Stmt {

	private final Stmt stmt;
	private final Expr<IntType> iterations;

	private static final int HASH_SEED = 361;
	private static final String STMT_LABEL = "loop";

	private volatile int hashCode = 0;

	private LoopStmt(final Stmt stmt, final Expr<IntType> iterations) {
		this.stmt = stmt;
		this.iterations = iterations;
	}

	public static LoopStmt of(final Stmt stmt, final Expr<IntType> iterations) {
		return new LoopStmt(stmt, iterations);
	}

	public Stmt getStmt() {
		return stmt;
	}

	public Expr<IntType> getIterations() {
		return iterations;
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
			result = 37 * result + stmt.hashCode();
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
			return this.getStmt().equals(that.getStmt());
		} else {
			return false;
		}
	}

	@Override
	public String toString() {
		return Utils.lispStringBuilder(STMT_LABEL).add(iterations.toString()+" "+stmt).toString();
	}

}
