package hu.bme.mit.theta.core.utils;

import hu.bme.mit.theta.core.stmt.*;
import hu.bme.mit.theta.core.type.Type;

public class StmtCounterVisitor implements StmtVisitor<Void, Integer> {

	private static final class LazyHolder {
		private final static StmtCounterVisitor INSTANCE = new StmtCounterVisitor();
	}

	private StmtCounterVisitor() {
	}

	public static StmtCounterVisitor getInstance() {
		return StmtCounterVisitor.LazyHolder.INSTANCE;
	}

	@Override
	public Integer visit(SkipStmt stmt, Void param) {
		return 1;
	}

	@Override
	public Integer visit(AssumeStmt stmt, Void param) {
		return 1;
	}

	@Override
	public <DeclType extends Type> Integer visit(AssignStmt<DeclType> stmt, Void param) {
		return 1;
	}

	@Override
	public <DeclType extends Type> Integer visit(HavocStmt<DeclType> stmt, Void param) {
		return 1;
	}

	@Override
	public Integer visit(SequenceStmt stmt, Void param) {
		int count = 0;
		for (var subStmt: stmt.getStmts()){
			count+=subStmt.accept(this,null);
		}
		return count+1;
	}

	@Override
	public Integer visit(NonDetStmt stmt, Void param) {
		int count = 0;
		for (var subStmt: stmt.getStmts()){
			count+=subStmt.accept(this,null);
		}
		return count+1;
	}

	@Override
	public Integer visit(OrtStmt stmt, Void param) {
		int count = 0;
		for (var subStmt: stmt.getStmts()){
			count+=subStmt.accept(this,null);
		}
		return count+1;
	}
}
