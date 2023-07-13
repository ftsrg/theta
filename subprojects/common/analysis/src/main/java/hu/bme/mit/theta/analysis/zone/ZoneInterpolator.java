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

import hu.bme.mit.theta.analysis.algorithm.lazy.itp.Interpolator;

import java.util.Collection;

public final class ZoneInterpolator implements Interpolator<ZoneState, ZoneState> {

    private static final ZoneInterpolator INSTANCE = new ZoneInterpolator();

    private ZoneInterpolator() {
    }

    public static ZoneInterpolator getInstance() {
        return INSTANCE;
    }

    @Override
    public ZoneState toItpDom(final ZoneState zone) {
        return zone;
    }

    @Override
    public ZoneState interpolate(final ZoneState zone1, final ZoneState zone2) {
        return ZoneState.interpolant(zone1, zone2);
    }

    @Override
    public Collection<ZoneState> complement(final ZoneState zone) {
        return zone.complement();
    }

    @Override
    public boolean refutes(final ZoneState zone1, final ZoneState zone2) {
        return !zone1.isConsistentWith(zone2);
    }
}
