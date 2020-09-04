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

import hu.bme.mit.theta.xcfa.XCFA;
import hu.bme.mit.theta.xcfa.alt.expl.ExecutableTransitionBase;
import hu.bme.mit.theta.xcfa.alt.expl.ImmutableExplState;
import hu.bme.mit.theta.xcfa.alt.expl.LocalityUtils;
import hu.bme.mit.theta.xcfa.alt.expl.Transition;

import javax.annotation.Nullable;

/**
 * An explicit checker traversing every possible ordering of an XCFA state.
 * Supports only zero-initialized values (because of how ExplState works).
 */
final class ExplicitChecker extends XcfaChecker{

    @Override
    protected void onNodePushed(DfsNodeBase node) {
        //
    }

    @Override
    protected DfsNode initialNode(ImmutableExplState state) {
        return new DfsNode(state, null);
    }

    ExplicitChecker(XCFA xcfa, Config config) {
        super(xcfa,config);
    }

    private final class DfsNode extends DfsNodeBase {

        DfsNode(ImmutableExplState state, @Nullable Transition lastTransition) {
            super(state, lastTransition);
            if (config.optimizeLocals()) {
                var l = LocalityUtils.findAnyEnabledLocalProcessTransition(state);
                if (l.isPresent()) {
                    push(l.get());
                    return;
                }
            }
            expand();
        }

        @Override
        public DfsNodeBase nodeFrom(ImmutableExplState state, ExecutableTransitionBase lastTransition) {
            return new DfsNode(state, lastTransition);
        }
    }
}
