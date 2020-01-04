package hu.bme.mit.theta.xcfa.simulator;

import com.google.common.base.Preconditions;
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
import hu.bme.mit.theta.xcfa.dsl.CallStmt;

/**
 * Updates state without checking enabledness. Does not update locations.
 * Uses the StmtExecutorInterface to decouple from CallState (and thus ExplState).
 */
public class StateUpdateVisitor implements XcfaStmtVisitor<StmtExecutorInterface, Void> {

	private StateUpdateVisitor() {
	}

	private static StateUpdateVisitor instance;

	public static StateUpdateVisitor getInstance() {
		if (instance == null) instance = new StateUpdateVisitor();
		return instance;
	}

	@Override
	public Void visit(XcfaCallStmt _stmt, StmtExecutorInterface param) {
		Preconditions.checkArgument(_stmt instanceof CallStmt, "XcfaCallStmt should be a CallStmt!");
		CallStmt stmt = (CallStmt) _stmt;
		param.onCall(stmt);
		// paraméterek befelé: stmt.getParams()
		// az, amit hívnak: stmt.getProcedure()
		// visszatérési értéket stmt.getVar()-ba kell írni
		return null;
	}

	@Override
	public Void visit(StoreStmt storeStmt, StmtExecutorInterface param) {
		throw new UnsupportedOperationException("Not yet supported");
	}

	@Override
	public Void visit(LoadStmt loadStmt, StmtExecutorInterface param) {
		throw new UnsupportedOperationException("Not yet supported");
	}

	@Override
	public Void visit(AtomicBeginStmt atomicBeginStmt, StmtExecutorInterface param) {
		param.onAtomicBegin();
		return null;
	}

	@Override
	public Void visit(AtomicEndStmt atomicEndStmt, StmtExecutorInterface param) {
		param.onAtomicEnd();
		return null;
	}

	@Override
	public Void visit(NotifyAllStmt notifyAllStmt, StmtExecutorInterface param) {
		throw new UnsupportedOperationException("Not yet supported");
	}

	@Override
	public Void visit(NotifyStmt notifyStmt, StmtExecutorInterface param) {
		throw new UnsupportedOperationException("Not yet supported");
	}

	@Override
	public Void visit(WaitStmt waitStmt, StmtExecutorInterface param) {
		throw new UnsupportedOperationException("Not yet supported");
	}

	@Override
	public Void visit(SkipStmt stmt, StmtExecutorInterface param) {
		return null;
	}

	@Override
	public Void visit(AssumeStmt stmt, StmtExecutorInterface param) {
		return null;
	}

	@Override
	public <DeclType extends Type> Void visit(AssignStmt<DeclType> stmt, StmtExecutorInterface param) {
		param.onAssign(stmt);
		return null;
	}

	@Override
	public <DeclType extends Type> Void visit(HavocStmt<DeclType> stmt, StmtExecutorInterface param) {
		param.onHavoc(stmt);
		return null;
	}

	@Override
	public Void visit(XcfaStmt xcfaStmt, StmtExecutorInterface param) {
		return xcfaStmt.accept(this, param);
	}

}
