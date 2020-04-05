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
import hu.bme.mit.theta.core.stmt.xcfa.LockStmt;
import hu.bme.mit.theta.core.stmt.xcfa.UnlockStmt;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.xcfa.dsl.CallStmt;

/**
 * An adapter for XcfaStmtVisitor.
 * The XcfaStmtVisitor is too powerful for such an easy use case.
 * This is a much nicer interface (at least for me).
 * TODO maybe this is not needed?
 */
public interface StmtExecutorInterface {
	<DeclType extends Type> void onAssign(AssignStmt<DeclType> stmt);

	<DeclType extends Type> void onHavoc(HavocStmt<DeclType> stmt);

	void onCall(CallStmt stmt);

	boolean onAssume(AssumeStmt stmt);

	void onAtomicBegin();

	void onAtomicEnd();

	boolean canLock(LockStmt lockStmt); // TODO

	boolean canUnlock(UnlockStmt unlockStmt);

	void lock(LockStmt lockStmt);

	void unlock(UnlockStmt unlockStmt);
}