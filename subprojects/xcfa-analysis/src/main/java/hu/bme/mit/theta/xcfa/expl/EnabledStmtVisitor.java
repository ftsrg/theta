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

import hu.bme.mit.theta.core.stmt.AssignStmt;
import hu.bme.mit.theta.core.stmt.AssumeStmt;
import hu.bme.mit.theta.core.stmt.HavocStmt;
import hu.bme.mit.theta.core.stmt.SkipStmt;
import hu.bme.mit.theta.core.stmt.XcfaStmt;
import hu.bme.mit.theta.core.stmt.xcfa.*;
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
		return true;
	}

	@Override
	public Boolean visit(AtomicEndStmt atomicEndStmt, StmtExecutorInterface param) {
		return true;
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

	@Override
	public Boolean visit(LockStmt lockStmt, StmtExecutorInterface param) {
		return param.canLock(lockStmt);
	}

	@Override
	public Boolean visit(UnlockStmt unlockStmt, StmtExecutorInterface param) {
		return param.canUnlock(unlockStmt);
	}

	@Override
	public Boolean visit(ExitWaitStmt exitWaitStmt, StmtExecutorInterface param) {
		throw new UnsupportedOperationException("Not yet supported");
	}

	@Override
	public Boolean visit(EnterWaitStmt enterWaitStmt, StmtExecutorInterface param) {
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
