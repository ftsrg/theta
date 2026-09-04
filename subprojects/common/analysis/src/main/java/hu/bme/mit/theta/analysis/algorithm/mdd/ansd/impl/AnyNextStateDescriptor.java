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

/**
 * Accepts any continuation: every value leads to {@code child}, with no source constraint (a {@link
 * AbstractNextStateDescriptor.Postcondition} whose off-diagonal is the diagonal under every source).
 * The self-looping {@link #ANY} singleton accepts everything below it — the bound's data-boundary cut
 * and the identity of the {@link AndNextStateDescriptor} postcondition intersection.
 */
public class AnyNextStateDescriptor implements AbstractNextStateDescriptor.Postcondition {
    private static final UniqueTable<AnyNextStateDescriptor> uniqueTable =
            UniqueTable.newInstance();

    public static final AbstractNextStateDescriptor.Postcondition ANY = new AnyNextStateDescriptor();

    public static AbstractNextStateDescriptor withChild(AbstractNextStateDescriptor child) {
        return uniqueTable.checkIn(new AnyNextStateDescriptor(child));
    }

    private final AbstractNextStateDescriptor child;

    private AnyNextStateDescriptor() {
        this.child = this;
    }

    private AnyNextStateDescriptor(AbstractNextStateDescriptor child) {
        this.child = child;
    }

    @Override
    public boolean evaluate() {
        return true;
    }

    @Override
    public IntObjMapView<AbstractNextStateDescriptor> getValuations(StateSpaceInfo localStateSpace) {
        return IntObjMapView.empty(child);
    }

    @Override
    public Optional<Iterable<AbstractNextStateDescriptor>> split() {
        return Optional.empty();
    }
}
