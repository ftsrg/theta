/*
 *  Copyright 2024 Budapest University of Technology and Economics
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
package hu.bme.mit.theta.analysis.algorithm.symbolic.model.impl;

import java.util.Optional;

import hu.bme.mit.delta.collections.IntObjMapView;
import hu.bme.mit.theta.analysis.algorithm.symbolic.model.AbstractNextStateDescriptor;
import hu.bme.mit.theta.analysis.algorithm.symbolic.model.StateSpaceInfo;

public final class EmptyNextStateDescriptor implements AbstractNextStateDescriptor {
    private EmptyNextStateDescriptor() {
    }

    public static final EmptyNextStateDescriptor INSTANCE = new EmptyNextStateDescriptor();

    @Override
    public IntObjMapView<AbstractNextStateDescriptor> getDiagonal(StateSpaceInfo localStateSpace) {
        // TODO: cache this instead of creating on demand
        return IntObjMapView.empty(INSTANCE);
    }

    @Override
    public IntObjMapView<IntObjMapView<AbstractNextStateDescriptor>> getOffDiagonal(
            StateSpaceInfo localStateSpace) {
        // TODO: cache this instead of creating on demand
        return IntObjMapView.empty(IntObjMapView.empty(INSTANCE));
    }

    @Override
    public Optional<Iterable<AbstractNextStateDescriptor>> split() {
        return Optional.empty();
    }

    @Override
    public boolean evaluate() {
        return false;
    }
}
