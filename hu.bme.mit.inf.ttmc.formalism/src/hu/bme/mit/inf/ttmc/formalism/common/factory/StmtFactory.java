package hu.bme.mit.inf.ttmc.formalism.common.factory;

import java.util.List;

import com.google.common.collect.ImmutableList;

import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.type.BoolType;
import hu.bme.mit.inf.ttmc.constraint.type.Type;
import hu.bme.mit.inf.ttmc.formalism.common.decl.VarDecl;
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

public interface StmtFactory {

	public AssumeStmt Assume(final Expr<? extends BoolType> cond);

	public AssertStmt Assert(final Expr<? extends BoolType> cond);

	public <T1 extends Type, T2 extends T1> AssignStmt<T1, T2> Assign(final VarDecl<T1> varDecl, final Expr<T2> expr);

	public <T extends Type> HavocStmt<T> Havoc(final VarDecl<T> varDecl);

	public BlockStmt Block(final List<? extends Stmt> stmts);

	public default BlockStmt Block(final Stmt... stmts) {
		return Block(ImmutableList.copyOf(stmts));
	}

	public <T extends Type> ReturnStmt<T> Return(final Expr<? extends T> expr);

	public IfStmt If(final Expr<? extends BoolType> cond, final Stmt then);

	public IfElseStmt If(final Expr<? extends BoolType> cond, final Stmt then, final Stmt elze);

	public WhileStmt While(final Expr<? extends BoolType> cond, final Stmt stmt);

	public DoStmt Do(final Stmt stmt, final Expr<? extends BoolType> cond);

	public SkipStmt Skip();

}
