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

import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.xcfa.XCFA;

import java.util.Collection;

/**
 * A transition with an associated edge.
 * Almost every transition is alike, except LeaveTransition, at the moment.
 * Uses StmtExecutorInterface through EnabledStmtVisitor and StateUpdateVisitor to process statements.
 * An exception is LeaveTransition, which leaves a call.
 *
 * A transition instance should be independent of ExplStates.
 *
 * Note: In the future, to be able to cache these transitions, one should not store state of the explicit state in use.
 *
 * Note: Multiple statements on the same edge is not supported.
 *   Enabledness cannot be determined without running previous stmts
 *   Function calls will mess everything up
 *
 * Abstract so I can "mock" it in the tests (without actually using ugly reflection)
 */
public abstract class StmtTransition extends ProcessTransition {

	public StmtTransition(XCFA.Process p) {
		super(p);
	}

	@Override
	public abstract void execute(ExplState state);

	@Override
	public abstract boolean enabled(ExplState state);

	// read vars that don't change
	public abstract Collection<VarDecl<?>> getRWVars();

	// read vars that do change
	public abstract Collection<VarDecl<?>> getWVars();
}
