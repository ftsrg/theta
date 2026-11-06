/*
 *  Copyright 2026 Budapest University of Technology and Economics
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
package hu.bme.mit.theta.xta.analysis.zone;

import static com.google.common.base.Preconditions.checkNotNull;

import com.google.common.collect.ImmutableList;
import hu.bme.mit.theta.analysis.InitFunc;
import hu.bme.mit.theta.analysis.zone.ZonePrec;
import hu.bme.mit.theta.analysis.zone.ZoneState;
import hu.bme.mit.theta.xta.XtaProcess.Loc;
import hu.bme.mit.theta.xta.XtaSystem;
import java.util.Collection;
import java.util.Collections;
import java.util.List;

final class XtaZoneInitFunc implements InitFunc<ZoneState, ZonePrec> {

    private final List<Loc> initLocs;

    private XtaZoneInitFunc(final XtaSystem system) {
        initLocs = ImmutableList.copyOf(system.getInitLocs());
    }

    static XtaZoneInitFunc create(final XtaSystem system) {
        return new XtaZoneInitFunc(checkNotNull(system));
    }

    @Override
    public Collection<ZoneState> getInitStates(final ZonePrec prec) {
        checkNotNull(prec);
        // Initial invariants are not applied here: post applies them to the source anyway, and a
        // bottom initial state would break the lazy checker.
        final ZoneState.Builder builder = ZoneState.zero(prec.getVars()).transform();
        if (XtaZoneUtils.shouldApplyDelay(initLocs)) {
            XtaZoneUtils.applyDelay(builder);
        }
        return Collections.singleton(builder.build());
    }
}
