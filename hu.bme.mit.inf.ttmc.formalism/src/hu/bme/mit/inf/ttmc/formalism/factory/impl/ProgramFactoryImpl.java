package hu.bme.mit.inf.ttmc.formalism.factory.impl;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;

import java.util.HashMap;
import java.util.List;

import hu.bme.mit.inf.ttmc.constraint.decl.ParamDecl;
import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.type.BoolType;
import hu.bme.mit.inf.ttmc.constraint.type.Type;
import hu.bme.mit.inf.ttmc.formalism.decl.ProcDecl;
import hu.bme.mit.inf.ttmc.formalism.decl.VarDecl;
import hu.bme.mit.inf.ttmc.formalism.decl.impl.ProcDeclImpl;
import hu.bme.mit.inf.ttmc.formalism.decl.impl.VarDeclImpl;
import hu.bme.mit.inf.ttmc.formalism.expr.PrimedExpr;
import hu.bme.mit.inf.ttmc.formalism.expr.ProcCallExpr;
import hu.bme.mit.inf.ttmc.formalism.expr.ProcRefExpr;
import hu.bme.mit.inf.ttmc.formalism.expr.VarRefExpr;
import hu.bme.mit.inf.ttmc.formalism.expr.impl.PrimedExprImpl;
import hu.bme.mit.inf.ttmc.formalism.expr.impl.ProcCallExprImpl;
import hu.bme.mit.inf.ttmc.formalism.expr.impl.ProcRefExprImpl;
import hu.bme.mit.inf.ttmc.formalism.expr.impl.VarRefExprImpl;
import hu.bme.mit.inf.ttmc.formalism.factory.ProgramFactory;
import hu.bme.mit.inf.ttmc.formalism.stmt.AssertStmt;
import hu.bme.mit.inf.ttmc.formalism.stmt.AssignStmt;
import hu.bme.mit.inf.ttmc.formalism.stmt.AssumeStmt;
import hu.bme.mit.inf.ttmc.formalism.stmt.BlockStmt;
import hu.bme.mit.inf.ttmc.formalism.stmt.DoStmt;
import hu.bme.mit.inf.ttmc.formalism.stmt.HavocStmt;
import hu.bme.mit.inf.ttmc.formalism.stmt.IfElseStmt;
import hu.bme.mit.inf.ttmc.formalism.stmt.IfStmt;
import hu.bme.mit.inf.ttmc.formalism.stmt.ReturnStmt;
import hu.bme.mit.inf.ttmc.formalism.stmt.SkipStmt;
import hu.bme.mit.inf.ttmc.formalism.stmt.Stmt;
import hu.bme.mit.inf.ttmc.formalism.stmt.WhileStmt;
import hu.bme.mit.inf.ttmc.formalism.stmt.impl.AssertStmtImpl;
import hu.bme.mit.inf.ttmc.formalism.stmt.impl.AssignStmtImpl;
import hu.bme.mit.inf.ttmc.formalism.stmt.impl.AssumeStmtImpl;
import hu.bme.mit.inf.ttmc.formalism.stmt.impl.BlockStmtImpl;
import hu.bme.mit.inf.ttmc.formalism.stmt.impl.DoStmtImpl;
import hu.bme.mit.inf.ttmc.formalism.stmt.impl.HavocStmtImpl;
import hu.bme.mit.inf.ttmc.formalism.stmt.impl.IfElseStmtImpl;
import hu.bme.mit.inf.ttmc.formalism.stmt.impl.IfStmtImpl;
import hu.bme.mit.inf.ttmc.formalism.stmt.impl.ReturnStmtImpl;
import hu.bme.mit.inf.ttmc.formalism.stmt.impl.SkipStmtImpl;
import hu.bme.mit.inf.ttmc.formalism.stmt.impl.WhileStmtImpl;
import hu.bme.mit.inf.ttmc.formalism.type.ProcType;
import hu.bme.mit.inf.ttmc.formalism.type.impl.ProcTypeImpl;

public class ProgramFactoryImpl implements ProgramFactory {

	private final HashMap<String, VarDecl<?>> nameToVar;
	private final HashMap<String, ProcDecl<?>> nameToProc;
	
	private final SkipStmt skipStmt;
	
	public ProgramFactoryImpl() {
		nameToVar = new HashMap<>();
		nameToProc = new HashMap<>();
		skipStmt = new SkipStmtImpl();
	}
	
	////
	
	@Override
	public <T extends Type> VarDecl<T> Var(final String name, final T type) {
		checkNotNull(name);
		checkNotNull(type);
		checkArgument(name.length() > 0);
		checkArgument(nameToVar.get(name) == null);
		
		final VarDecl<T> varDecl = new VarDeclImpl<>(name, type);
		nameToVar.put(name, varDecl);
		return varDecl;
	}
	
	@Override
	public <R extends Type> ProcDecl<R> Proc(String name, List<? extends ParamDecl<? extends Type>> paramDecls, R returnType) {
		checkNotNull(name);
		checkNotNull(paramDecls);
		checkNotNull(returnType);
		checkArgument(name.length() > 0);
		checkArgument(nameToProc.get(name) == null);
		
		final ProcDecl<R> procDecl = new ProcDeclImpl<>(name, paramDecls, returnType);
		nameToProc.put(name, procDecl);
		return procDecl;
	}
	
	////

	@Override
	public <R extends Type> ProcType<R> Proc(List<? extends Type> paramTypes, R returnType) {
		checkNotNull(paramTypes);
		checkNotNull(returnType);
		return new ProcTypeImpl<>(paramTypes, returnType);
	}
	
	////
	
	@Override
	public <T extends Type> VarRefExpr<T> Ref(VarDecl<T> varDecl) {
		checkNotNull(varDecl);
		return new VarRefExprImpl<>(varDecl);
	}
	
	@Override
	public <R extends Type> ProcRefExpr<R> Ref(ProcDecl<R> procDecl) {
		checkNotNull(procDecl);
		return new ProcRefExprImpl<>(procDecl);
	}
	
	@Override
	public <R extends Type> ProcCallExpr<R> Call(Expr<? extends ProcType<? extends R>> proc,
			List<? extends Expr<?>> params) {
		checkNotNull(proc);
		checkNotNull(params);
		return new ProcCallExprImpl<>(proc, params);
	}

	@Override
	public <T extends Type> PrimedExpr<T> Prime(Expr<? extends T> op) {
		checkNotNull(op);
		return new PrimedExprImpl<>(op);
	}
	
	////

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
