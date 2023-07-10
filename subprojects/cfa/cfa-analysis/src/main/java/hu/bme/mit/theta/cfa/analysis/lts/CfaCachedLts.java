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
package hu.bme.mit.theta.cfa.analysis.lts;

import java.util.Collection;

import hu.bme.mit.theta.common.container.Containers;

import java.util.Map;

import hu.bme.mit.theta.cfa.CFA.Loc;
import hu.bme.mit.theta.cfa.analysis.CfaAction;
import hu.bme.mit.theta.cfa.analysis.CfaState;

/**
 * A caching layer over CFA LTS implementations. It only computes actions for each location once and
 * stores the result for later queries.
 */
public final class CfaCachedLts implements CfaLts {

    private final CfaLts lts;
    private final Map<Loc, Collection<CfaAction>> actionCache;

    public CfaCachedLts(final CfaLts lts) {
        this.lts = lts;
        this.actionCache = Containers.createMap();
    }

    @Override
    public Collection<CfaAction> getEnabledActionsFor(final CfaState<?> state) {
        final Loc loc = state.getLoc();
        if (!actionCache.containsKey(loc)) {
            actionCache.put(loc, lts.getEnabledActionsFor(state));
        }
        return actionCache.get(loc);
    }

}
