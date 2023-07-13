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

import hu.bme.mit.theta.analysis.Lattice;
import hu.bme.mit.theta.analysis.PartialOrd;

public final class ZoneLattice implements Lattice<ZoneState> {

    private final PartialOrd<ZoneState> partialOrd;

    private static final ZoneLattice INSTANCE = new ZoneLattice();

    private ZoneLattice() {
        partialOrd = ZoneOrd.getInstance();
    }

    public static ZoneLattice getInstance() {
        return INSTANCE;
    }

    @Override
    public ZoneState top() {
        return ZoneState.top();
    }

    @Override
    public ZoneState bottom() {
        return ZoneState.bottom();
    }

    @Override
    public ZoneState meet(final ZoneState state1, final ZoneState state2) {
        return ZoneState.intersection(state1, state2);
    }

    @Override
    public ZoneState join(final ZoneState state1, final ZoneState state2) {
        return ZoneState.enclosure(state1, state2);
    }

    @Override
    public boolean isLeq(final ZoneState state1, final ZoneState state2) {
        return partialOrd.isLeq(state1, state2);
    }
}
