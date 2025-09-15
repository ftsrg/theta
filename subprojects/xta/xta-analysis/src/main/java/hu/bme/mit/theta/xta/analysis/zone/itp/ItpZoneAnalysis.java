/*
 *  Copyright 2025 Budapest University of Technology and Economics
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
package hu.bme.mit.theta.xta.analysis.zone.itp;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.Analysis;
import hu.bme.mit.theta.analysis.InitFunc;
import hu.bme.mit.theta.analysis.PartialOrd;
import hu.bme.mit.theta.analysis.TransFunc;
import hu.bme.mit.theta.analysis.zone.ZonePrec;
import hu.bme.mit.theta.analysis.zone.ZoneState;

public final class ItpZoneAnalysis<A extends Action>
        implements Analysis<ItpZoneState, A, ZonePrec> {

    private final InitFunc<ItpZoneState, ZonePrec> initFunc;
    private final TransFunc<ItpZoneState, A, ZonePrec> transFunc;

    private ItpZoneAnalysis(final Analysis<ZoneState, ? super A, ZonePrec> analysis) {
        checkNotNull(analysis);
        initFunc = ItpZoneInitFunc.create(analysis.getInitFunc());
        transFunc = ItpZoneTransFunc.create(analysis.getTransFunc());
    }

    public static <A extends Action> ItpZoneAnalysis<A> create(
            final Analysis<ZoneState, ? super A, ZonePrec> analysis) {
        return new ItpZoneAnalysis<>(analysis);
    }

    ////

    @Override
    public PartialOrd<ItpZoneState> getPartialOrd() {
        return ItpZoneOrd.getInstance();
    }

    @Override
    public InitFunc<ItpZoneState, ZonePrec> getInitFunc() {
        return initFunc;
    }

    @Override
    public TransFunc<ItpZoneState, A, ZonePrec> getTransFunc() {
        return transFunc;
    }
}
