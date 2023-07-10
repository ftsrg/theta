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

package hu.bme.mit.theta.xcfa.analysis.impl.singlethread;

import hu.bme.mit.theta.analysis.LTS;
import hu.bme.mit.theta.xcfa.model.XcfaEdge;
import hu.bme.mit.theta.xcfa.model.XcfaLocation;
import hu.bme.mit.theta.xcfa.passes.processpass.FunctionInlining;

import java.util.ArrayList;
import java.util.Collection;

public final class XcfaSTLts implements LTS<XcfaSTState<?>, XcfaSTAction> {

    @Override
    public Collection<XcfaSTAction> getEnabledActionsFor(final XcfaSTState<?> state) {
        final Collection<XcfaSTAction> xcfaActions = new ArrayList<>();
        final XcfaLocation loc = state.getCurrentLoc();
        for (XcfaEdge outgoingEdge : loc.getOutgoingEdges()) {
            final XcfaSTAction xcfaAction =
                FunctionInlining.inlining == FunctionInlining.InlineFunctions.ON ?
                    XcfaSTAction.create(outgoingEdge) :
                    XcfaSTAction.createWithVars(outgoingEdge,
                        ((XcfaSTStateStack<?>) state).getCurrentVars());
            xcfaActions.add(xcfaAction);
        }
        return xcfaActions;
    }

}
