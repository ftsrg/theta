package hu.bme.mit.inf.ttmc.formalism.common.factory.impl;

import static com.google.common.base.Preconditions.checkNotNull;

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
import hu.bme.mit.inf.ttmc.formalism.common.stmt.DoStmt;
import hu.bme.mit.inf.ttmc.formalism.common.stmt.HavocStmt;
import hu.bme.mit.inf.ttmc.formalism.common.stmt.IfElseStmt;
import hu.bme.mit.inf.ttmc.formalism.common.stmt.IfStmt;
import hu.bme.mit.inf.ttmc.formalism.common.stmt.ReturnStmt;
import hu.bme.mit.inf.ttmc.formalism.common.stmt.SkipStmt;
import hu.bme.mit.inf.ttmc.formalism.common.stmt.Stmt;
import hu.bme.mit.inf.ttmc.formalism.common.stmt.WhileStmt;
import hu.bme.mit.inf.ttmc.formalism.common.stmt.impl.AssertStmtImpl;
import hu.bme.mit.inf.ttmc.formalism.common.stmt.impl.AssignStmtImpl;
import hu.bme.mit.inf.ttmc.formalism.common.stmt.impl.AssumeStmtImpl;
import hu.bme.mit.inf.ttmc.formalism.common.stmt.impl.BlockStmtImpl;
import hu.bme.mit.inf.ttmc.formalism.common.stmt.impl.DoStmtImpl;
import hu.bme.mit.inf.ttmc.formalism.common.stmt.impl.HavocStmtImpl;
import hu.bme.mit.inf.ttmc.formalism.common.stmt.impl.IfElseStmtImpl;
import hu.bme.mit.inf.ttmc.formalism.common.stmt.impl.IfStmtImpl;
import hu.bme.mit.inf.ttmc.formalism.common.stmt.impl.ReturnStmtImpl;
import hu.bme.mit.inf.ttmc.formalism.common.stmt.impl.SkipStmtImpl;
import hu.bme.mit.inf.ttmc.formalism.common.stmt.impl.WhileStmtImpl;

public class StmtFactoryImpl implements StmtFactory {

	private final SkipStmt skipStmt;

	public StmtFactoryImpl() {
		skipStmt = new SkipStmtImpl();
	}

	@Override
	public AssumeStmt Assume(final Expr<? extends BoolType> cond) {
		checkNotNull(cond);
		return new AssumeStmtImpl(cond);
	}

	@Override
	public AssertStmt Assert(final Expr<? extends BoolType> cond) {
		checkNotNull(cond);
		return new AssertStmtImpl(cond);
	}

	@Override
	public <T1 extends Type, T2 extends T1> AssignStmt<T1, T2> Assign(final VarDecl<T1> lhs, final Expr<T2> rhs) {
		checkNotNull(lhs);
		checkNotNull(rhs);
		return new AssignStmtImpl<>(lhs, rhs);
	}

	@Override
	public <T extends Type> HavocStmt<T> Havoc(final VarDecl<T> varDecl) {
		checkNotNull(varDecl);
		return new HavocStmtImpl<>(varDecl);
	}

	@Override
	public BlockStmt Block(final List<? extends Stmt> stmts) {
		checkNotNull(stmts);
		return new BlockStmtImpl(stmts);
	}

	@Override
	public <T extends Type> ReturnStmt<T> Return(final Expr<? extends T> expr) {
		checkNotNull(expr);
		return new ReturnStmtImpl<>(expr);
	}

	@Override
	public IfStmt If(final Expr<? extends BoolType> cond, final Stmt then) {
		checkNotNull(cond);
		checkNotNull(then);
		return new IfStmtImpl(cond, then);
	}

	@Override
	public IfElseStmt If(final Expr<? extends BoolType> cond, final Stmt then, final Stmt elze) {
		checkNotNull(cond);
		checkNotNull(then);
		checkNotNull(elze);
		return new IfElseStmtImpl(cond, then, elze);
	}

	@Override
	public WhileStmt While(final Expr<? extends BoolType> cond, final Stmt stmt) {
		checkNotNull(cond);
		checkNotNull(stmt);
		return new WhileStmtImpl(cond, stmt);
	}

	@Override
	public DoStmt Do(final Stmt stmt, final Expr<? extends BoolType> cond) {
		checkNotNull(stmt);
		checkNotNull(cond);
		return new DoStmtImpl(stmt, cond);
	}

	@Override
	public SkipStmt Skip() {
		return skipStmt;
	}

}
