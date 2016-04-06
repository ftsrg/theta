package hu.bme.mit.inf.ttmc.formalism.common.stmt.impl;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.List;
import java.util.StringJoiner;

import com.google.common.collect.ImmutableList;

import hu.bme.mit.inf.ttmc.formalism.common.stmt.BlockStmt;
import hu.bme.mit.inf.ttmc.formalism.common.stmt.Stmt;

public final class BlockStmtImpl extends AbstractStmt implements BlockStmt {

	private static final int HASH_SEED = 757;
	private volatile int hashCode = 0;

	private final List<? extends Stmt> stmts;

	public BlockStmtImpl(final List<? extends Stmt> stmts) {
		this.stmts = ImmutableList.copyOf(checkNotNull(stmts));
	}

	@Override
	public List<? extends Stmt> getStmts() {
		return stmts;
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
