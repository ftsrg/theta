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

/**
 * A transition is the atomic unit of execution.
 *
 * This interface is used to update the state.
 *
 * Mostly corresponds to one statement. (Exception: LeaveTransition)
 *
 * A transition instance should be independent of ExplStates.
 * Thus, a transition could be cached later.
 *
 * 	   For this, a procedure wrapper was created (ProcedureData)
 *
 * TODO decouple from ExplState? (use a State interface instead)
 */
public interface Transition {

	/**
	 * Updates the runtime state by the transition
	 * Should be called only by ExplState.
	 * @param state The ExplState to be updated
	 */
	void execute(ExplState state);

	/**
	 * Checks whether a transition is enabled.
	 * @param state The current state
	 * @return Returns whether this transition is enabled
	 */
	boolean enabled(ExplState state);
}
