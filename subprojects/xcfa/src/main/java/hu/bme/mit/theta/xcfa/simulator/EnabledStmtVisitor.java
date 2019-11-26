package hu.bme.mit.theta.xcfa.simulator;

import hu.bme.mit.theta.core.stmt.*;
import hu.bme.mit.theta.core.stmt.xcfa.*;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.booltype.BoolLitExpr;

public class EnabledStmtVisitor implements XcfaStmtVisitor<RuntimeState, Boolean> {

	@Override
	public Boolean visit(SkipStmt stmt, RuntimeState param) {
		return true;
	}

	@Override
	public Boolean visit(AssumeStmt stmt, RuntimeState state) {
		BoolLitExpr a = (BoolLitExpr) state.evalExpr(stmt.getCond());
		return a.getValue();
	}

	@Override
	public <DeclType extends Type> Boolean visit(AssignStmt<DeclType> stmt, RuntimeState param) {
		return true;
	}

	@Override
	public <DeclType extends Type> Boolean visit(HavocStmt<DeclType> stmt, RuntimeState param) {
		return true;
	}

	@Override
	public Boolean visit(XcfaStmt xcfaStmt, RuntimeState param) {
		// TODO is this safe? return xcfaStmt.accept(this, param);
		return xcfaStmt.accept((XcfaStmtVisitor<RuntimeState, Boolean>) this, param);
	}

	@Override
	public Boolean visit(XcfaCallStmt stmt, RuntimeState param) {
		return true;
	}

	@Override
	public Boolean visit(StoreStmt storeStmt, RuntimeState param) {
		throw new UnsupportedOperationException("Not yet supported");
	}

	@Override
	public Boolean visit(LoadStmt loadStmt, RuntimeState param) {
		throw new UnsupportedOperationException("Not yet supported");
	}

	@Override
	public Boolean visit(AtomicBeginStmt atomicBeginStmt, RuntimeState param) {
		throw new UnsupportedOperationException("Not yet supported");
	}

	@Override
	public Boolean visit(AtomicEndStmt atomicEndStmt, RuntimeState param) {
		throw new UnsupportedOperationException("Not yet supported");
	}

	@Override
	public Boolean visit(NotifyAllStmt notifyAllStmt, RuntimeState param) {
		throw new UnsupportedOperationException("Not yet supported");
	}

	@Override
	public Boolean visit(NotifyStmt notifyStmt, RuntimeState param) {
		throw new UnsupportedOperationException("Not yet supported");
	}

	@Override
	public Boolean visit(WaitStmt waitStmt, RuntimeState param) {
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
