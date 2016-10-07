package hu.bme.mit.theta.core.utils.impl;

import java.util.Collection;

import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.stmt.AssertStmt;
import hu.bme.mit.theta.core.stmt.AssignStmt;
import hu.bme.mit.theta.core.stmt.AssumeStmt;
import hu.bme.mit.theta.core.stmt.BlockStmt;
import hu.bme.mit.theta.core.stmt.DeclStmt;
import hu.bme.mit.theta.core.stmt.DoStmt;
import hu.bme.mit.theta.core.stmt.HavocStmt;
import hu.bme.mit.theta.core.stmt.IfElseStmt;
import hu.bme.mit.theta.core.stmt.IfStmt;
import hu.bme.mit.theta.core.stmt.ReturnStmt;
import hu.bme.mit.theta.core.stmt.SkipStmt;
import hu.bme.mit.theta.core.stmt.WhileStmt;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.utils.StmtVisitor;

final class VarCollectorStmtVisitor implements StmtVisitor<Collection<VarDecl<?>>, Void> {

	private final static VarCollectorStmtVisitor INSTANCE = new VarCollectorStmtVisitor();
	private final static VarCollectorExprVisitor EXPR_VISITOR = VarCollectorExprVisitor.getInstance();

	private VarCollectorStmtVisitor() {
	}

	static VarCollectorStmtVisitor getInstance() {
		return INSTANCE;
	}

	@Override
	public Void visit(final SkipStmt stmt, final Collection<VarDecl<?>> vars) {
		return null;
	}

	@Override
	public <DeclType extends Type, ExprType extends DeclType> Void visit(final DeclStmt<DeclType, ExprType> stmt,
			final Collection<VarDecl<?>> vars) {
		vars.add(stmt.getVarDecl());
		if (stmt.getInitVal().isPresent()) {
			stmt.getInitVal().get().accept(EXPR_VISITOR, vars);
		}
		return null;
	}

	@Override
	public Void visit(final AssumeStmt stmt, final Collection<VarDecl<?>> vars) {
		stmt.getCond().accept(EXPR_VISITOR, vars);
		return null;
	}

	@Override
	public Void visit(final AssertStmt stmt, final Collection<VarDecl<?>> vars) {
		stmt.getCond().accept(EXPR_VISITOR, vars);
		return null;
	}

	@Override
	public <DeclType extends Type, ExprType extends DeclType> Void visit(final AssignStmt<DeclType, ExprType> stmt,
			final Collection<VarDecl<?>> vars) {
		vars.add(stmt.getVarDecl());
		stmt.getExpr().accept(EXPR_VISITOR, vars);
		return null;
	}

	@Override
	public <DeclType extends Type> Void visit(final HavocStmt<DeclType> stmt, final Collection<VarDecl<?>> vars) {
		vars.add(stmt.getVarDecl());
		return null;
	}

	@Override
	public Void visit(final BlockStmt stmt, final Collection<VarDecl<?>> vars) {
		stmt.getStmts().forEach(s -> s.accept(this, vars));
		return null;
	}

	@Override
	public <ReturnType extends Type> Void visit(final ReturnStmt<ReturnType> stmt, final Collection<VarDecl<?>> vars) {
		stmt.getExpr().accept(EXPR_VISITOR, vars);
		return null;
	}

	@Override
	public Void visit(final IfStmt stmt, final Collection<VarDecl<?>> vars) {
		stmt.getCond().accept(EXPR_VISITOR, vars);
		stmt.getThen().accept(this, vars);
		return null;
	}

	@Override
	public Void visit(final IfElseStmt stmt, final Collection<VarDecl<?>> vars) {
		stmt.getCond().accept(EXPR_VISITOR, vars);
		stmt.getThen().accept(this, vars);
		stmt.getElse().accept(this, vars);
		return null;
	}

	@Override
	public Void visit(final WhileStmt stmt, final Collection<VarDecl<?>> vars) {
		stmt.getCond().accept(EXPR_VISITOR, vars);
		stmt.getDo().accept(this, vars);
		return null;
	}

	@Override
	public Void visit(final DoStmt stmt, final Collection<VarDecl<?>> vars) {
		stmt.getCond().accept(EXPR_VISITOR, vars);
		stmt.getDo().accept(this, vars);
		return null;
	}

}
