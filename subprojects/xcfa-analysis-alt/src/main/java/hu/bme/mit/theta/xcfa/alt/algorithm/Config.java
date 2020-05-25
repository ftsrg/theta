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
package hu.bme.mit.theta.xcfa.alt.algorithm;

/**
 * A config might be inconsistent, always check before usage.
 * TODO reimplement as a simple Map<string, ?>
 */
public interface Config {
    boolean rememberTraces();
    boolean debug();
    /**
     * Optimize when there is a process with only local transitions,
     *  at least one of them being local.
     */
    boolean optimizeLocals();
    boolean discardAlreadyExplored();
    /**
     * Reduce state graph with partial order reduction techniques
     */
    boolean isPartialOrder();

    /**
     * Force iterate every trace, do not exit, when an unsafe property is found
     */
    boolean forceIterate();

    /**
     * Simple Partial order reduction technique
     * @return
     */
    boolean isAmpleSet();

    class ImmutableConfig implements Config {
        private final boolean rememberTraces;
        private final boolean debug;
        private final boolean optimizeLocals;
        private final boolean discardAlreadyExplored;
        private final boolean partialOrder;
        private final boolean forceIterate;
        private final boolean ampleSet;

        private ImmutableConfig(boolean rememberTraces, boolean debug, boolean optimizeLocals, boolean discardAlreadyExplored, boolean partialOrder, boolean forceIterate, boolean ampleSet) {
            this.rememberTraces = rememberTraces;
            this.debug = debug;
            this.optimizeLocals = optimizeLocals;
            this.discardAlreadyExplored = discardAlreadyExplored;
            this.partialOrder = partialOrder;
            this.forceIterate = forceIterate;
            this.ampleSet = ampleSet;
        }

        @Override
        public boolean rememberTraces() {
            return rememberTraces;
        }

        @Override
        public boolean debug() {
            return debug;
        }

        @Override
        public boolean optimizeLocals() {
            return optimizeLocals;
        }

        @Override
        public boolean discardAlreadyExplored() {
            return discardAlreadyExplored;
        }

        @Override
        public boolean isPartialOrder() {
            return partialOrder;
        }

        @Override
        public boolean forceIterate() {
            return forceIterate;
        }

        @Override
        public boolean isAmpleSet() {
            return ampleSet;
        }
    }

    public class Builder {
        public boolean rememberTraces = false;
        public boolean debug = false;
        public boolean optimizeLocals = false;
        public boolean discardAlreadyExplored = false;
        public boolean partialOrder = false;
        public boolean forceIterate = false;
        public boolean ampleSet = false;

        public Config build() {
            return new ImmutableConfig(rememberTraces, debug, optimizeLocals, discardAlreadyExplored, partialOrder, forceIterate, ampleSet);
        }
    }
}
