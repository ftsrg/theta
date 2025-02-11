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
package hu.bme.mit.theta.analysis.algorithm.mdd.ansd.impl;

import hu.bme.mit.delta.collections.IntObjMapView;
import hu.bme.mit.delta.collections.UniqueTable;
import hu.bme.mit.theta.analysis.algorithm.mdd.ansd.AbstractNextStateDescriptor;
import hu.bme.mit.theta.analysis.algorithm.mdd.ansd.StateSpaceInfo;
import java.util.Optional;

public class AnyNextStateDescriptor implements AbstractNextStateDescriptor {
    private static final UniqueTable<AnyNextStateDescriptor> uniqueTable =
            UniqueTable.newInstance();

    public static AbstractNextStateDescriptor withChild(AbstractNextStateDescriptor child) {
        return uniqueTable.checkIn(new AnyNextStateDescriptor(child));
    }

    private final AbstractNextStateDescriptor child;

    private AnyNextStateDescriptor(AbstractNextStateDescriptor child) {
        this.child = child;
    }

    @Override
    public boolean isNextStateDefined() {
        return false;
    }

    @Override
    public IntObjMapView<AbstractNextStateDescriptor> getDiagonal(StateSpaceInfo localStateSpace) {
        return IntObjMapView.empty(child);
    }

    @Override
    public IntObjMapView<IntObjMapView<AbstractNextStateDescriptor>> getOffDiagonal(
            final StateSpaceInfo localStateSpace) {
        return IntObjMapView.empty(IntObjMapView.empty(child));
    }

    @Override
    public Optional<Iterable<AbstractNextStateDescriptor>> split() {
        // TODO: this might be a performance overhead
        return Optional.empty();
    }
}
