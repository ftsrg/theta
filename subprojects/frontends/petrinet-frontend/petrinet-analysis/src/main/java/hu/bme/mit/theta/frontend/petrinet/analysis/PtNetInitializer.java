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
package hu.bme.mit.theta.frontend.petrinet.analysis;

import hu.bme.mit.delta.collections.IntObjMapView;
import hu.bme.mit.theta.analysis.algorithm.mdd.ansd.AbstractNextStateDescriptor;
import hu.bme.mit.theta.analysis.algorithm.mdd.ansd.StateSpaceInfo;
import hu.bme.mit.theta.frontend.petrinet.model.Place;

public final class PtNetInitializer implements AbstractNextStateDescriptor.Postcondition {
    private Place assignedPlace;
    private int initialMarking;
    private AbstractNextStateDescriptor continuation;

    public PtNetInitializer(
            final Place assignedPlace,
            final int initialMarking,
            final AbstractNextStateDescriptor continuation) {
        this.assignedPlace = assignedPlace;
        this.initialMarking = initialMarking;
        this.continuation = continuation;
    }

    @Override
    public IntObjMapView<AbstractNextStateDescriptor> getValuations(
            final StateSpaceInfo localStateSpace) {
        if (assignedPlace == localStateSpace.getTraceInfo()) {
            return IntObjMapView.singleton(initialMarking, continuation);
        } else {
            return IntObjMapView.empty(continuation);
        }
    }
}
