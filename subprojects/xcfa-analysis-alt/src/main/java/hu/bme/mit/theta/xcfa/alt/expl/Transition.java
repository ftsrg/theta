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
package hu.bme.mit.theta.xcfa.alt.expl;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.xcfa.XCFA;

import java.util.Optional;
import java.util.Set;

/**
 * Represents a state change.
 * Main method is enabled(), which returns an executable interface, when the transition is enabled.
 * It is assumed that a Transition only changes state of globals and exactly one process.
 */
public interface Transition extends Action {
    /**
     * Returns an executorInterface that mutates the state.
     * The passed state does not have to be mutable.
     * The executorInterface has to be passed a state that is mutable (and equivalent in
     * every way to the state passed here).
     * So care must be taken to couple these two calls.
     * @param state A state which is not mutated(!).
     * @return Returns empty when disabled, otherwise an executor interface to mutate the state.
     */
    Optional<TransitionExecutorInterface> enabled(ExplState state);

    /**
     * Auxiliary method for checking dependency of two transitions.
     * We are interested only in global variables.
     * Must be a subset of getRWVars().
     * Might return null if the list of variables cannot be determined.
     *   When null is returned, optimisations based on variables must be turned off.
     * @return The list of modified variables. Might contain local variables too. Null if it cannot be determined.
     */
    Set<VarDecl<? extends Type>> getWVars();

    /**
     * Auxiliary method for checking dependency of two transitions.
     * We are interested only in global variables.
     * Must be a superset of getWVars().
     * Might return null if the list of variables cannot be determined.
     *   When null is returned, optimisations based on variables must be turned off.
     * @return The list of accessed variables. Might contain local variables too. Null if it cannot be determined.
     */
    Set<VarDecl<? extends Type>> getRWVars();

    /**
     * The one process whose local variables and location is accessed (aside from global vars).
     * **Note** that there must be only one such process due to many reasons
     * laid down in multiple parts of the code.
     * When needed, a synchronized transition could be split in such a way
     * that they are equivalent to the original one, but only one process is accessed
     * at a time.
     * @return returns the single process that is accessed.
     */
    XCFA.Process getProcess();

    /**
     * Auxiliary function for checking states that do not change global variables.
     * Simplified version: local transitions can always be executed before
     * any other state.
     * LocalityUtils provides a more complete and more correct explanation.
     * @return Returns true when the transition does not access global variables.
     */
    boolean isLocal();
}
