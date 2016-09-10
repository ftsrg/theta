package hu.bme.mit.theta.formalism.utils;

import java.util.Collections;
import java.util.List;
import java.util.stream.Collectors;

import hu.bme.mit.theta.formalism.common.stmt.BlockStmt;
import hu.bme.mit.theta.formalism.common.stmt.Stmt;

public class StmtUtils {

	private StmtUtils() {
	}

	public static List<? extends Stmt> getSubStmts(final Stmt stmt) {
		if (stmt instanceof BlockStmt) {
			final BlockStmt blockStmt = (BlockStmt) stmt;
			return blockStmt.getStmts().stream().map(s -> getSubStmts(s)).flatMap(c -> c.stream())
					.collect(Collectors.toList());
		} else {
			return Collections.singletonList(stmt);
		}
	}

}
