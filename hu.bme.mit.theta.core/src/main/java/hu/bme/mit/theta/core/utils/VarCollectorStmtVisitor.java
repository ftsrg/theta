package hu.bme.mit.theta.core.utils;

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

final class VarCollectorStmtVisitor implements StmtVisitor<Collection<VarDecl<?>>, Void> {

	private static final class LazyHolder {
		private final static VarCollectorStmtVisitor INSTANCE = new VarCollectorStmtVisitor();
	}

	private VarCollectorStmtVisitor() {
	}

	static VarCollectorStmtVisitor getInstance() {
		return LazyHolder.INSTANCE;
	}

	@Override
	public Void visit(final SkipStmt stmt, final Collection<VarDecl<?>> vars) {
		return null;
	}

	@Override
	public <DeclType extends Type> Void visit(final DeclStmt<DeclType> stmt, final Collection<VarDecl<?>> vars) {
		vars.add(stmt.getVarDecl());
		if (stmt.getInitVal().isPresent()) {
			ExprUtils.collectVars(stmt.getInitVal().get(), vars);
		}
		return null;
	}

	@Override
	public Void visit(final AssumeStmt stmt, final Collection<VarDecl<?>> vars) {
		ExprUtils.collectVars(stmt.getCond(), vars);
		return null;
	}

	@Override
	public Void visit(final AssertStmt stmt, final Collection<VarDecl<?>> vars) {
		ExprUtils.collectVars(stmt.getCond(), vars);
		return null;
	}

	@Override
	public <DeclType extends Type> Void visit(final AssignStmt<DeclType> stmt, final Collection<VarDecl<?>> vars) {
		vars.add(stmt.getVarDecl());
		ExprUtils.collectVars(stmt.getExpr(), vars);
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
		ExprUtils.collectVars(stmt.getExpr(), vars);
		return null;
	}

	@Override
	public Void visit(final IfStmt stmt, final Collection<VarDecl<?>> vars) {
		ExprUtils.collectVars(stmt.getCond(), vars);
		stmt.getThen().accept(this, vars);
		return null;
	}

	@Override
	public Void visit(final IfElseStmt stmt, final Collection<VarDecl<?>> vars) {
		ExprUtils.collectVars(stmt.getCond(), vars);
		stmt.getThen().accept(this, vars);
		stmt.getElse().accept(this, vars);
		return null;
	}

	@Override
	public Void visit(final WhileStmt stmt, final Collection<VarDecl<?>> vars) {
		ExprUtils.collectVars(stmt.getCond(), vars);
		stmt.getDo().accept(this, vars);
		return null;
	}

	@Override
	public Void visit(final DoStmt stmt, final Collection<VarDecl<?>> vars) {
		ExprUtils.collectVars(stmt.getCond(), vars);
		stmt.getDo().accept(this, vars);
		return null;
	}

}
