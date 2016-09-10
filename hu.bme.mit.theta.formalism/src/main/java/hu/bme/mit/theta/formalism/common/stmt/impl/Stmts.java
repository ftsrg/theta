package hu.bme.mit.theta.formalism.common.stmt.impl;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.List;

import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.type.BoolType;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.formalism.common.decl.VarDecl;
import hu.bme.mit.theta.formalism.common.stmt.AssertStmt;
import hu.bme.mit.theta.formalism.common.stmt.AssignStmt;
import hu.bme.mit.theta.formalism.common.stmt.AssumeStmt;
import hu.bme.mit.theta.formalism.common.stmt.BlockStmt;
import hu.bme.mit.theta.formalism.common.stmt.DeclStmt;
import hu.bme.mit.theta.formalism.common.stmt.DoStmt;
import hu.bme.mit.theta.formalism.common.stmt.HavocStmt;
import hu.bme.mit.theta.formalism.common.stmt.IfElseStmt;
import hu.bme.mit.theta.formalism.common.stmt.IfStmt;
import hu.bme.mit.theta.formalism.common.stmt.ReturnStmt;
import hu.bme.mit.theta.formalism.common.stmt.SkipStmt;
import hu.bme.mit.theta.formalism.common.stmt.Stmt;
import hu.bme.mit.theta.formalism.common.stmt.WhileStmt;

public class Stmts {

	private static final SkipStmt SKIP_STMT;

	static {
		SKIP_STMT = new SkipStmtImpl();
	}

	protected Stmts() {
	}

	public static <T extends Type> DeclStmt<T, ?> Decl(final VarDecl<T> varDecl) {
		checkNotNull(varDecl);
		return new DeclStmtImpl<>(varDecl);
	}

	public static <T1 extends Type, T2 extends T1> DeclStmt<T1, T2> Decl(final VarDecl<T1> varDecl,
			final Expr<T2> initVal) {
		checkNotNull(varDecl);
		checkNotNull(initVal);
		return new DeclStmtImpl<T1, T2>(varDecl, initVal);
	}

	public static AssumeStmt Assume(final Expr<? extends BoolType> cond) {
		checkNotNull(cond);
		return new AssumeStmtImpl(cond);
	}

	public static AssertStmt Assert(final Expr<? extends BoolType> cond) {
		checkNotNull(cond);
		return new AssertStmtImpl(cond);
	}

	public static <T1 extends Type, T2 extends T1> AssignStmt<T1, T2> Assign(final VarDecl<T1> lhs,
			final Expr<T2> rhs) {
		checkNotNull(lhs);
		checkNotNull(rhs);
		return new AssignStmtImpl<>(lhs, rhs);
	}

	public static <T extends Type> HavocStmt<T> Havoc(final VarDecl<T> varDecl) {
		checkNotNull(varDecl);
		return new HavocStmtImpl<>(varDecl);
	}

	public static BlockStmt Block(final List<? extends Stmt> stmts) {
		checkNotNull(stmts);
		return new BlockStmtImpl(stmts);
	}

	public static <T extends Type> ReturnStmt<T> Return(final Expr<? extends T> expr) {
		checkNotNull(expr);
		return new ReturnStmtImpl<>(expr);
	}

	public static IfStmt If(final Expr<? extends BoolType> cond, final Stmt then) {
		checkNotNull(cond);
		checkNotNull(then);
		return new IfStmtImpl(cond, then);
	}

	public static IfElseStmt If(final Expr<? extends BoolType> cond, final Stmt then, final Stmt elze) {
		checkNotNull(cond);
		checkNotNull(then);
		checkNotNull(elze);
		return new IfElseStmtImpl(cond, then, elze);
	}

	public static WhileStmt While(final Expr<? extends BoolType> cond, final Stmt stmt) {
		checkNotNull(cond);
		checkNotNull(stmt);
		return new WhileStmtImpl(cond, stmt);
	}

	public static DoStmt Do(final Stmt stmt, final Expr<? extends BoolType> cond) {
		checkNotNull(stmt);
		checkNotNull(cond);
		return new DoStmtImpl(stmt, cond);
	}

	public static SkipStmt Skip() {
		return SKIP_STMT;
	}

}
