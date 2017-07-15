package hu.bme.mit.theta.core.utils;

import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;

import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.stmt.BlockStmt;
import hu.bme.mit.theta.core.stmt.Stmt;

/**
 * Utility functions related to statements.
 */
public final class StmtUtils {

	private StmtUtils() {
	}

	/**
	 * Get sub statements of a statement
	 *
	 * @param stmt Statement
	 * @return List of sub statements
	 */
	public static List<? extends Stmt> getSubStmts(final Stmt stmt) {
		if (stmt instanceof BlockStmt) {
			final BlockStmt blockStmt = (BlockStmt) stmt;
			return blockStmt.getStmts().stream().map(s -> getSubStmts(s)).flatMap(c -> c.stream())
					.collect(Collectors.toList());
		} else {
			return Collections.singletonList(stmt);
		}
	}

	/**
	 * Get variables appearing in a statement
	 *
	 * @param stmt Statement
	 * @return Variables
	 */
	public static Set<VarDecl<?>> getVars(final Stmt stmt) {
		final Set<VarDecl<?>> vars = new HashSet<>();
		stmt.accept(VarCollectorStmtVisitor.getInstance(), vars);
		return vars;
	}

	/**
	 * Get variables appearing in statements
	 *
	 * @param stmts Statements
	 * @return Variables
	 */
	public static Set<VarDecl<?>> getVars(final Iterable<? extends Stmt> stmts) {
		final Set<VarDecl<?>> vars = new HashSet<>();
		stmts.forEach(s -> s.accept(VarCollectorStmtVisitor.getInstance(), vars));
		return vars;
	}

	/**
	 * Unfold a statement into expressions with a given indexing
	 *
	 * @param stmt Statement
	 * @param indexing Indexing
	 * @return Expressions and new indexing
	 */
	public static StmtUnfoldResult toExpr(final Stmt stmt, final VarIndexing indexing) {
		return StmtToExprTransformer.toExpr(stmt, indexing);
	}

	/**
	 * Unfold statements into expressions with a given indexing
	 *
	 * @param stmts Statements
	 * @param indexing Indexing
	 * @return Expressions and new indexing
	 */
	public static StmtUnfoldResult toExpr(final List<? extends Stmt> stmts, final VarIndexing indexing) {
		return StmtToExprTransformer.toExpr(stmts, indexing);
	}

}
