/*
 *  Copyright 2022 Budapest University of Technology and Economics
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

package hu.bme.mit.theta.xcfa.analysis.impl.multithread;

import hu.bme.mit.theta.analysis.LTS;
import hu.bme.mit.theta.analysis.expr.ExprState;
import hu.bme.mit.theta.xcfa.model.XcfaEdge;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

public class XcfaProcessLTS<S extends ExprState> implements LTS<XcfaProcessState<S>, XcfaProcessAction> {
    @Override
    public Collection<XcfaProcessAction> getEnabledActionsFor(XcfaProcessState<S> state) {
        final List<XcfaProcessAction> ret = new ArrayList<>();
        for (XcfaEdge outgoingEdge : state.getLocation().getOutgoingEdges()) {
            final XcfaProcessAction xcfaProcessAction = new XcfaProcessAction(outgoingEdge);
            ret.add(xcfaProcessAction);
        }
        return ret;
    }
}
