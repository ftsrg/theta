package hu.bme.mit.theta.core.stmt;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.List;
import java.util.StringJoiner;

import com.google.common.collect.ImmutableList;

import hu.bme.mit.theta.core.utils.StmtVisitor;

public final class BlockStmt implements Stmt {

	private static final int HASH_SEED = 757;
	private volatile int hashCode = 0;

	private final List<? extends Stmt> stmts;

	BlockStmt(final List<? extends Stmt> stmts) {
		this.stmts = ImmutableList.copyOf(checkNotNull(stmts));
	}

	public List<? extends Stmt> getStmts() {
		return stmts;
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
			result = 31 * result + stmts.hashCode();
			hashCode = result;
		}
		return result;
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		} else if (obj instanceof BlockStmt) {
			final BlockStmt that = (BlockStmt) obj;
			return this.getStmts().equals(that.getStmts());
		} else {
			return false;
		}
	}

	@Override
	public String toString() {
		final StringJoiner sj = new StringJoiner(", ", "Block(", ")");
		for (final Stmt stmt : stmts) {
			sj.add(stmt.toString());
		}
		return sj.toString();
	}

}
