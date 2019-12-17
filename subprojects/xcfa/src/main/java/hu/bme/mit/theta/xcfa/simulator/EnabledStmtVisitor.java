package hu.bme.mit.theta.xcfa.simulator;

import hu.bme.mit.theta.core.stmt.AssignStmt;
import hu.bme.mit.theta.core.stmt.AssumeStmt;
import hu.bme.mit.theta.core.stmt.HavocStmt;
import hu.bme.mit.theta.core.stmt.SkipStmt;
import hu.bme.mit.theta.core.stmt.XcfaStmt;
import hu.bme.mit.theta.core.stmt.xcfa.AtomicBeginStmt;
import hu.bme.mit.theta.core.stmt.xcfa.AtomicEndStmt;
import hu.bme.mit.theta.core.stmt.xcfa.LoadStmt;
import hu.bme.mit.theta.core.stmt.xcfa.NotifyAllStmt;
import hu.bme.mit.theta.core.stmt.xcfa.NotifyStmt;
import hu.bme.mit.theta.core.stmt.xcfa.StoreStmt;
import hu.bme.mit.theta.core.stmt.xcfa.WaitStmt;
import hu.bme.mit.theta.core.stmt.xcfa.XcfaCallStmt;
import hu.bme.mit.theta.core.stmt.xcfa.XcfaStmtVisitor;
import hu.bme.mit.theta.core.type.Type;

/**
 * Used to test if a given edge is active.
 * Only Wait and Assume can be inactive at a time.
 */
public class EnabledStmtVisitor implements XcfaStmtVisitor<StmtExecutorInterface, Boolean> {

	@Override
	public Boolean visit(SkipStmt stmt, StmtExecutorInterface param) {
		return true;
	}

	@Override
	public Boolean visit(AssumeStmt stmt, StmtExecutorInterface state) {
		return state.onAssume(stmt);
	}

	@Override
	public <DeclType extends Type> Boolean visit(AssignStmt<DeclType> stmt, StmtExecutorInterface param) {
		return true;
	}

	@Override
	public <DeclType extends Type> Boolean visit(HavocStmt<DeclType> stmt, StmtExecutorInterface param) {
		return true;
	}

	@Override
	public Boolean visit(XcfaStmt xcfaStmt, StmtExecutorInterface param) {
		return xcfaStmt.accept(this, param);
	}

	@Override
	public Boolean visit(XcfaCallStmt stmt, StmtExecutorInterface param) {
		return true;
	}

	@Override
	public Boolean visit(StoreStmt storeStmt, StmtExecutorInterface param) {
		throw new UnsupportedOperationException("Not yet supported");
	}

	@Override
	public Boolean visit(LoadStmt loadStmt, StmtExecutorInterface param) {
		throw new UnsupportedOperationException("Not yet supported");
	}

	@Override
	public Boolean visit(AtomicBeginStmt atomicBeginStmt, StmtExecutorInterface param) {
		throw new UnsupportedOperationException("Not yet supported");
	}

	@Override
	public Boolean visit(AtomicEndStmt atomicEndStmt, StmtExecutorInterface param) {
		throw new UnsupportedOperationException("Not yet supported");
	}

	@Override
	public Boolean visit(NotifyAllStmt notifyAllStmt, StmtExecutorInterface param) {
		throw new UnsupportedOperationException("Not yet supported");
	}

	@Override
	public Boolean visit(NotifyStmt notifyStmt, StmtExecutorInterface param) {
		throw new UnsupportedOperationException("Not yet supported");
	}

	@Override
	public Boolean visit(WaitStmt waitStmt, StmtExecutorInterface param) {
		throw new UnsupportedOperationException("Not yet supported");
	}

	private EnabledStmtVisitor() {
	}

	private static EnabledStmtVisitor instance;

	public static EnabledStmtVisitor getInstance() {
		if (instance == null) instance = new EnabledStmtVisitor();
		return instance;
	}

}
