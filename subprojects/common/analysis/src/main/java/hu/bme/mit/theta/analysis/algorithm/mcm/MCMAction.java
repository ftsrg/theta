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

public abstract class MCMAction<A extends Action> implements Action {
    private final A action;

    protected MCMAction(final A action) {
        this.action = action;
    }

    public abstract boolean isEmpty();

    public abstract MCMEventAction<A> asEventAction();

    public A getAction() {
        return action;
    }

    public static final class MCMEmptyAction<A extends Action> extends MCMAction<A> {
        private MCMEmptyAction(A action) {
            super(action);
        }

        public static <A extends Action> MCMEmptyAction<A> create(A action) {
            return new MCMEmptyAction<>(action);
        }

        @Override
        public boolean isEmpty() {
            return true;
        }

        @Override
        public MCMEventAction<A> asEventAction() {
            throw new RuntimeException("Cannot cast empty action to event action");
        }
    }

    public static final class MCMEventAction<A extends Action> extends MCMAction<A> {
        private final String type;
        private final String tag;

        private MCMEventAction(final String type, final String tag, final A action) {
            super(action);
            this.type = type;
            this.tag = tag;
        }

        @Override
        public boolean isEmpty() {
            return false;
        }

        @Override
        public MCMEventAction<A> asEventAction() {
            return this;
        }

        public String getType() {
            return type;
        }

        public String getTag() {
            return tag;
        }
    }
}
