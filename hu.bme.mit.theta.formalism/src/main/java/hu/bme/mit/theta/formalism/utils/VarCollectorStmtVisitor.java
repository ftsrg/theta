package hu.bme.mit.theta.formalism.utils;

import java.util.Collection;

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
import hu.bme.mit.theta.formalism.common.stmt.WhileStmt;

final class VarCollectorStmtVisitor implements StmtVisitor<Collection<VarDecl<?>>, Void> {

	private static VarCollectorStmtVisitor INSTANCE = new VarCollectorStmtVisitor();
	private static VarCollectorExprVisitor EXPR_VISITOR = VarCollectorExprVisitor.getInstance();

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
