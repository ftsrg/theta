package hu.bme.mit.theta.core.stmt;

import static com.google.common.base.Preconditions.checkNotNull;
import static java.util.Arrays.asList;

import java.util.List;

import hu.bme.mit.theta.core.Expr;
import hu.bme.mit.theta.core.Type;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.booltype.BoolType;

public class Stmts {

	private static final SkipStmt SKIP_STMT;

	static {
		SKIP_STMT = new SkipStmt();
	}

	protected Stmts() {
	}

	public static <T extends Type> DeclStmt<T> Decl(final VarDecl<T> varDecl) {
		checkNotNull(varDecl);
		return new DeclStmt<>(varDecl);
	}

	public static <T extends Type> DeclStmt<T> Decl(final VarDecl<T> varDecl, final Expr<T> initVal) {
		checkNotNull(varDecl);
		checkNotNull(initVal);
		return new DeclStmt<>(varDecl, initVal);
	}

	public static AssumeStmt Assume(final Expr<BoolType> cond) {
		checkNotNull(cond);
		return new AssumeStmt(cond);
	}

	public static AssertStmt Assert(final Expr<BoolType> cond) {
		checkNotNull(cond);
		return new AssertStmt(cond);
	}

	public static <T extends Type> AssignStmt<T> Assign(final VarDecl<T> lhs, final Expr<T> rhs) {
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

	public static <T extends Type> ReturnStmt<T> Return(final Expr<T> expr) {
		checkNotNull(expr);
		return new ReturnStmt<>(expr);
	}

	public static IfStmt If(final Expr<BoolType> cond, final Stmt then) {
		checkNotNull(cond);
		checkNotNull(then);
		return new IfStmt(cond, then);
	}

	public static IfElseStmt If(final Expr<BoolType> cond, final Stmt then, final Stmt elze) {
		checkNotNull(cond);
		checkNotNull(then);
		checkNotNull(elze);
		return new IfElseStmt(cond, then, elze);
	}

	public static WhileStmt While(final Expr<BoolType> cond, final Stmt stmt) {
		checkNotNull(cond);
		checkNotNull(stmt);
		return new WhileStmt(cond, stmt);
	}

	public static DoStmt Do(final Stmt stmt, final Expr<BoolType> cond) {
		checkNotNull(stmt);
		checkNotNull(cond);
		return new DoStmt(stmt, cond);
	}

	public static SkipStmt Skip() {
		return SKIP_STMT;
	}

}
