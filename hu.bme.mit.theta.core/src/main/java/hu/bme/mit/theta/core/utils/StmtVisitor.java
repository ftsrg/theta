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

	R visit(SkipStmt stmt, P param);

	<DeclType extends Type> R visit(DeclStmt<DeclType> stmt, P param);

	R visit(AssumeStmt stmt, P param);

	R visit(AssertStmt stmt, P param);

	<DeclType extends Type> R visit(AssignStmt<DeclType> stmt, P param);

	<DeclType extends Type> R visit(HavocStmt<DeclType> stmt, P param);

	R visit(BlockStmt stmt, P param);

	<ReturnType extends Type> R visit(ReturnStmt<ReturnType> stmt, P param);

	R visit(IfStmt stmt, P param);

	R visit(IfElseStmt stmt, P param);

	R visit(WhileStmt stmt, P param);

	R visit(DoStmt stmt, P param);

}
