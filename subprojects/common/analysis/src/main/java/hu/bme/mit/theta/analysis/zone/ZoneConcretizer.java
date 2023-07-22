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
package hu.bme.mit.theta.analysis.zone;

import hu.bme.mit.theta.analysis.PartialOrd;
import hu.bme.mit.theta.analysis.algorithm.lazy.itp.Concretizer;

public final class ZoneConcretizer implements Concretizer<ZoneState, ZoneState> {

    private final static ZoneConcretizer INSTANCE = new ZoneConcretizer();

    private final PartialOrd<ZoneState> ord;

    private ZoneConcretizer() {
        ord = ZoneOrd.getInstance();
    }

    public static ZoneConcretizer getInstance() {
        return INSTANCE;
    }

    @Override
    public ZoneState concretize(ZoneState state) {
        return state;
    }

    @Override
    public boolean proves(ZoneState state1, ZoneState state2) {
        return ord.isLeq(state1, state2);
    }

    @Override
    public boolean inconsistentConcrState(ZoneState state) {
        return state.isBottom();
    }
}
