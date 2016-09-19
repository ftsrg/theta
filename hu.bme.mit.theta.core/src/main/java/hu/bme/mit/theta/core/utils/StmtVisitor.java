package hu.bme.mit.theta.core.utils;

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

public interface StmtVisitor<P, R> {

	public R visit(SkipStmt stmt, P param);

	public <DeclType extends Type, ExprType extends DeclType> R visit(DeclStmt<DeclType, ExprType> stmt, P param);

	public R visit(AssumeStmt stmt, P param);

	public R visit(AssertStmt stmt, P param);

	public <DeclType extends Type, ExprType extends DeclType> R visit(AssignStmt<DeclType, ExprType> stmt, P param);

	public <DeclType extends Type> R visit(HavocStmt<DeclType> stmt, P param);

	public R visit(BlockStmt stmt, P param);

	public <ReturnType extends Type> R visit(ReturnStmt<ReturnType> stmt, P param);

	public R visit(IfStmt stmt, P param);

	public R visit(IfElseStmt stmt, P param);

	public R visit(WhileStmt stmt, P param);

	public R visit(DoStmt stmt, P param);

}
