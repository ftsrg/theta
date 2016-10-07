package hu.bme.mit.theta.core.utils.impl;

import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;

import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.stmt.BlockStmt;
import hu.bme.mit.theta.core.stmt.Stmt;
import hu.bme.mit.theta.core.type.Type;

public final class StmtUtils {

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

	public static Set<VarDecl<? extends Type>> getVars(final Stmt stmt) {
		final Set<VarDecl<? extends Type>> vars = new HashSet<>();
		stmt.accept(VarCollectorStmtVisitor.getInstance(), vars);
		return vars;
	}

	public static StmtToExprResult toExpr(final List<? extends Stmt> stmts, final VarIndexes indexes) {
		return StmtToExprTransformer.toExpr(stmts, indexes);
	}

}
