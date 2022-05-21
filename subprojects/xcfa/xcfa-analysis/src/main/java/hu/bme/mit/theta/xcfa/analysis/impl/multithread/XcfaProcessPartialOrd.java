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

import hu.bme.mit.theta.analysis.PartialOrd;
import hu.bme.mit.theta.analysis.expr.ExprState;

public class XcfaProcessPartialOrd<S extends ExprState> implements PartialOrd<XcfaProcessState<S>> {
    private final PartialOrd<S> partialOrd;

    public XcfaProcessPartialOrd(PartialOrd<S> partialOrd) {
        this.partialOrd = partialOrd;
    }

    @Override
    public boolean isLeq(XcfaProcessState<S> state1, XcfaProcessState<S> state2) {
        return state1.getLocation().equals(state2.getLocation()) && partialOrd.isLeq(state1.getState(), state2.getState());
    }
}
