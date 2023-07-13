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
package hu.bme.mit.theta.analysis.expl;

import hu.bme.mit.theta.analysis.PartialOrd;
import hu.bme.mit.theta.analysis.algorithm.lazy.itp.Concretizer;

public final class ExplConcretizer implements Concretizer<ExplState, ExplState> {

    private final static ExplConcretizer INSTANCE = new ExplConcretizer();

    private final PartialOrd<ExplState> ord;

    private ExplConcretizer() {
        ord = ExplOrd.getInstance();
    }

    public static ExplConcretizer getInstance() {
        return INSTANCE;
    }

    @Override
    public ExplState concretize(final ExplState state) {
        return state;
    }

    @Override
    public boolean proves(final ExplState state1, final ExplState state2) {
        return ord.isLeq(state1, state2);
    }

    @Override
    public boolean inconsistentConcrState(final ExplState state) {
        return state.isBottom();
    }
}
