/*
 *  Copyright 2017 Budapest University of Technology and Economics
 *
 *  Licensed under the Apache License, Version 2.0 (the "License");
 *  you may not use this file except in compliance with the License.
 *  You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 *  Unless required by applicable law or agreed to in writing, software
 *  distributed under the License is distributed on an "AS IS" BASIS,
 *  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *  See the License for the specific language governing permissions and
 *  limitations under the License.
 */
package hu.bme.mit.theta.xcfa.expl;

import com.google.common.base.Preconditions;
import hu.bme.mit.theta.core.stmt.AssignStmt;
import hu.bme.mit.theta.core.stmt.AssumeStmt;
import hu.bme.mit.theta.core.stmt.HavocStmt;
import hu.bme.mit.theta.core.stmt.SkipStmt;
import hu.bme.mit.theta.core.stmt.XcfaStmt;
import hu.bme.mit.theta.core.stmt.xcfa.*;
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
		// parameterek befele: stmt.getParams()
		// az, amit hivnak: stmt.getProcedure()
		// visszateresi erteket stmt.getVar()-ba kell irni
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
	public Void visit(LockStmt lockStmt, StmtExecutorInterface param) {
		param.lock(lockStmt);
		return null;
	}

	@Override
	public Void visit(UnlockStmt unlockStmt, StmtExecutorInterface param) {
		param.unlock(unlockStmt);
		return null;
	}

	@Override
	public Void visit(ExitWaitStmt exitWaitStmt, StmtExecutorInterface param) {
		throw new UnsupportedOperationException("Not yet supported");
	}

	@Override
	public Void visit(EnterWaitStmt enterWaitStmt, StmtExecutorInterface param) {
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
