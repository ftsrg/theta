package hu.bme.mit.inf.ttmc.formalism.common.factory.impl;

import java.util.List;

import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.type.BoolType;
import hu.bme.mit.inf.ttmc.constraint.type.Type;
import hu.bme.mit.inf.ttmc.formalism.common.decl.VarDecl;
import hu.bme.mit.inf.ttmc.formalism.common.factory.StmtFactory;
import hu.bme.mit.inf.ttmc.formalism.common.stmt.AssertStmt;
import hu.bme.mit.inf.ttmc.formalism.common.stmt.AssignStmt;
import hu.bme.mit.inf.ttmc.formalism.common.stmt.AssumeStmt;
import hu.bme.mit.inf.ttmc.formalism.common.stmt.BlockStmt;
import hu.bme.mit.inf.ttmc.formalism.common.stmt.DeclStmt;
import hu.bme.mit.inf.ttmc.formalism.common.stmt.DoStmt;
import hu.bme.mit.inf.ttmc.formalism.common.stmt.HavocStmt;
import hu.bme.mit.inf.ttmc.formalism.common.stmt.IfElseStmt;
import hu.bme.mit.inf.ttmc.formalism.common.stmt.IfStmt;
import hu.bme.mit.inf.ttmc.formalism.common.stmt.ReturnStmt;
import hu.bme.mit.inf.ttmc.formalism.common.stmt.SkipStmt;
import hu.bme.mit.inf.ttmc.formalism.common.stmt.Stmt;
import hu.bme.mit.inf.ttmc.formalism.common.stmt.WhileStmt;
import hu.bme.mit.inf.ttmc.formalism.common.stmt.impl.Stmts;

public class StmtFactoryImpl implements StmtFactory {

	@Override
	public <T extends Type> DeclStmt<T, ?> Decl(final VarDecl<T> varDecl) {
		return Stmts.Decl(varDecl);
	}

	@Override
	public <T1 extends Type, T2 extends T1> DeclStmt<T1, T2> Decl(final VarDecl<T1> varDecl, final Expr<T2> initVal) {
		return Stmts.Decl(varDecl, initVal);
	}

	@Override
	public AssumeStmt Assume(final Expr<? extends BoolType> cond) {
		return Stmts.Assume(cond);
	}

	@Override
	public AssertStmt Assert(final Expr<? extends BoolType> cond) {
		return Stmts.Assert(cond);
	}

	@Override
	public <T1 extends Type, T2 extends T1> AssignStmt<T1, T2> Assign(final VarDecl<T1> lhs, final Expr<T2> rhs) {
		return Stmts.Assign(lhs, rhs);
	}

	@Override
	public <T extends Type> HavocStmt<T> Havoc(final VarDecl<T> varDecl) {
		return Stmts.Havoc(varDecl);
	}

	@Override
	public BlockStmt Block(final List<? extends Stmt> stmts) {
		return Stmts.Block(stmts);
	}

	@Override
	public <T extends Type> ReturnStmt<T> Return(final Expr<? extends T> expr) {
		return Stmts.Return(expr);
	}

	@Override
	public IfStmt If(final Expr<? extends BoolType> cond, final Stmt then) {
		return Stmts.If(cond, then);
	}

	@Override
	public IfElseStmt If(final Expr<? extends BoolType> cond, final Stmt then, final Stmt elze) {
		return Stmts.If(cond, then, elze);
	}

	@Override
	public WhileStmt While(final Expr<? extends BoolType> cond, final Stmt stmt) {
		return Stmts.While(cond, stmt);
	}

	@Override
	public DoStmt Do(final Stmt stmt, final Expr<? extends BoolType> cond) {
		return Stmts.Do(stmt, cond);
	}

	@Override
	public SkipStmt Skip() {
		return Stmts.Skip();
	}

}
