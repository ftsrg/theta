/*
 *  Copyright 2023 Budapest University of Technology and Economics
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
package hu.bme.mit.theta.analysis.algorithm.lazy.itp;

import hu.bme.mit.theta.analysis.PartialOrd;
import hu.bme.mit.theta.analysis.State;

import static com.google.common.base.Preconditions.checkNotNull;

public final class BasicConcretizer<S extends State> implements Concretizer<S, S> {

    private final PartialOrd<S> ord;

    private BasicConcretizer(final PartialOrd<S> ord) {
        this.ord = checkNotNull(ord);
    }

    public static <S extends State> BasicConcretizer<S> create(final PartialOrd<S> ord) {
        return new BasicConcretizer<S>(ord);
    }

    @Override
    public final S concretize(final S state) {
        return state;
    }

    @Override
    public boolean proves(final S state1, final S state2) {
        return ord.isLeq(state1, state2);
    }

    @Override
    public boolean inconsistentConcrState(S state) {
        return state.isBottom();
    }
}
