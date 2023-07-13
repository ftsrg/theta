/*
 *  Copyright 2022 Budapest University of Technology and Economics
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

package hu.bme.mit.theta.analysis.algorithm.mcm;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.stmt.Stmt;

import java.util.Collection;
import java.util.List;
import java.util.Optional;

import static com.google.common.base.Preconditions.checkNotNull;

public interface MemoryEventProvider<S extends State, A extends Action> {

    /**
     * Gets a piecewise representation of an action, separating memory events from independent parts of the action.
     * It is required that the original action's effect stays the same when the piecewise representation is applied.
     *
     * @param action
     * @return
     */
    Collection<ResultElement<A>> getPiecewiseAction(S state, A action);

    int getVarId(VarDecl<?> var);

    A createAction(S s, List<Stmt> stmt);

    class ResultElement<A extends Action> {
        private final Optional<MemoryEvent> memoryEvent;
        private final Optional<A> action;

        public ResultElement(final MemoryEvent memoryEvent) {
            this.memoryEvent = Optional.of(checkNotNull(memoryEvent));
            this.action = Optional.empty();
        }

        public ResultElement(final A action) {
            this.memoryEvent = Optional.empty();
            this.action = Optional.of(checkNotNull(action));
        }

        public MemoryEvent getMemoryEvent() {
            return memoryEvent.orElseThrow();
        }

        public A getAction() {
            return action.orElseThrow();
        }

        public boolean isMemoryEvent() {
            return memoryEvent.isPresent();
        }

        public boolean isAction() {
            return action.isPresent();
        }

        @Override
        public String toString() {
            if (memoryEvent.isPresent()) return memoryEvent.get().toString();
            else return action.toString();
        }
    }

}