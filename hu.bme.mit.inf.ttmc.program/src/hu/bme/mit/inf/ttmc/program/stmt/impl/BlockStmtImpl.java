package hu.bme.mit.inf.ttmc.program.stmt.impl;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.List;
import java.util.StringJoiner;

import com.google.common.collect.ImmutableList;

import hu.bme.mit.inf.ttmc.program.stmt.BlockStmt;
import hu.bme.mit.inf.ttmc.program.stmt.Stmt;

public class BlockStmtImpl extends AbstractStmt implements BlockStmt {
	
	private final static int HASHSEED = 757;
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
		if (hashCode == 0) {
			hashCode = HASHSEED;
			hashCode = 37 * hashCode + stmts.hashCode();
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
			final BlockStmtImpl that = (BlockStmtImpl) obj;
			return this.stmts.equals(that.stmts);
		} else {
			return false;
		}
	}
	
	@Override
	public String toString() {
		final StringJoiner sj = new StringJoiner(", ", "Block(", ")");
		for (Stmt stmt : stmts) {
			sj.add(stmt.toString());
		}
		return sj.toString();
	}
	
}
