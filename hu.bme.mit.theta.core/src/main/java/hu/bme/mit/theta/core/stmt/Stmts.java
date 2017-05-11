package hu.bme.mit.theta.core.stmt;

import static com.google.common.base.Preconditions.checkNotNull;
import static java.util.Arrays.asList;

import java.util.List;

import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.type.BoolType;
import hu.bme.mit.theta.core.type.Type;

public class Stmts {

	private static final SkipStmt SKIP_STMT;

	static {
		SKIP_STMT = new SkipStmt();
	}

	protected Stmts() {
	}

	public static <T extends Type> DeclStmt<T, ?> Decl(final VarDecl<T> varDecl) {
		checkNotNull(varDecl);
		return new DeclStmt<>(varDecl);
	}

	public static <T1 extends Type, T2 extends T1> DeclStmt<T1, T2> Decl(final VarDecl<T1> varDecl,
			final Expr<T2> initVal) {
		checkNotNull(varDecl);
		checkNotNull(initVal);
		return new DeclStmt<>(varDecl, initVal);
	}

	public static AssumeStmt Assume(final Expr<? extends BoolType> cond) {
		checkNotNull(cond);
		return new AssumeStmt(cond);
	}

	public static AssertStmt Assert(final Expr<? extends BoolType> cond) {
		checkNotNull(cond);
		return new AssertStmt(cond);
	}

	public static <T1 extends Type, T2 extends T1> AssignStmt<T1, T2> Assign(final VarDecl<T1> lhs,
			final Expr<T2> rhs) {
		checkNotNull(lhs);
		checkNotNull(rhs);
		return new AssignStmt<>(lhs, rhs);
	}

	public static <T extends Type> HavocStmt<T> Havoc(final VarDecl<T> varDecl) {
		checkNotNull(varDecl);
		return new HavocStmt<>(varDecl);
	}

	public static BlockStmt Block(final List<? extends Stmt> stmts) {
		checkNotNull(stmts);
		return new BlockStmt(stmts);
	}

	public static BlockStmt Block(final Stmt... stmts) {
		return Block(asList(stmts));
	}

	public static <T extends Type> ReturnStmt<T> Return(final Expr<? extends T> expr) {
		checkNotNull(expr);
		return new ReturnStmt<>(expr);
	}

	public static IfStmt If(final Expr<? extends BoolType> cond, final Stmt then) {
		checkNotNull(cond);
		checkNotNull(then);
		return new IfStmt(cond, then);
	}

	public static IfElseStmt If(final Expr<? extends BoolType> cond, final Stmt then, final Stmt elze) {
		checkNotNull(cond);
		checkNotNull(then);
		checkNotNull(elze);
		return new IfElseStmt(cond, then, elze);
	}

	public static WhileStmt While(final Expr<? extends BoolType> cond, final Stmt stmt) {
		checkNotNull(cond);
		checkNotNull(stmt);
		return new WhileStmt(cond, stmt);
	}

	public static DoStmt Do(final Stmt stmt, final Expr<? extends BoolType> cond) {
		checkNotNull(stmt);
		checkNotNull(cond);
		return new DoStmt(stmt, cond);
	}

	public static SkipStmt Skip() {
		return SKIP_STMT;
	}

}
