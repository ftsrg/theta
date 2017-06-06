package hu.bme.mit.theta.core.utils;

import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;

import hu.bme.mit.theta.core.Type;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.stmt.BlockStmt;
import hu.bme.mit.theta.core.stmt.Stmt;

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

	public static Set<VarDecl<? extends Type>> getVars(final Iterable<? extends Stmt> stmts) {
		final Set<VarDecl<? extends Type>> vars = new HashSet<>();
		for (final Stmt stmt : stmts) {
			vars.addAll(getVars(stmt));
		}
		return vars;
	}

	public static UnfoldResult toExpr(final List<? extends Stmt> stmts, final VarIndexing indexing) {
		return StmtToExprTransformer.toExpr(stmts, indexing);
	}

}
