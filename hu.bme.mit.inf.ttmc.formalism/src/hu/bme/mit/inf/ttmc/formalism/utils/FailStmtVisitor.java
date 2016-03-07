package hu.bme.mit.inf.ttmc.formalism.utils;

import hu.bme.mit.inf.ttmc.constraint.type.Type;
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
import hu.bme.mit.inf.ttmc.formalism.stmt.WhileStmt;

public class FailStmtVisitor<P, R> implements StmtVisitor<P, R> {

	@Override
	public R visit(SkipStmt stmt, P param) {
		throw new UnsupportedOperationException();
	}

	@Override
	public R visit(AssumeStmt stmt, P param) {
		throw new UnsupportedOperationException();
	}

	@Override
	public R visit(AssertStmt stmt, P param) {
		throw new UnsupportedOperationException();
	}

	@Override
	public <LhsType extends Type, RhsType extends LhsType> R visit(AssignStmt<LhsType, RhsType> stmt, P param) {
		throw new UnsupportedOperationException();
	}

	@Override
	public <LhsType extends Type> R visit(HavocStmt<LhsType> stmt, P param) {
		throw new UnsupportedOperationException();
	}

	@Override
	public R visit(BlockStmt stmt, P param) {
		throw new UnsupportedOperationException();
	}
	
	@Override
	public <ReturnType extends Type> R visit(ReturnStmt<ReturnType> stmt, P param) {
		throw new UnsupportedOperationException();
	}

	@Override
	public R visit(IfStmt stmt, P param) {
		throw new UnsupportedOperationException();
	}

	@Override
	public R visit(IfElseStmt stmt, P param) {
		throw new UnsupportedOperationException();
	}

	@Override
	public R visit(WhileStmt stmt, P param) {
		throw new UnsupportedOperationException();
	}

	@Override
	public R visit(DoStmt stmt, P param) {
		throw new UnsupportedOperationException();
	}

}
