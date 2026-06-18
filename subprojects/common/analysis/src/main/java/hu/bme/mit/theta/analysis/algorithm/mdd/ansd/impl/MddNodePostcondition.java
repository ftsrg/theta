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

import com.google.common.base.Preconditions;
import hu.bme.mit.delta.collections.IntObjMapView;
import hu.bme.mit.delta.collections.impl.IntObjMapViews;
import hu.bme.mit.delta.java.mdd.MddHandle;
import hu.bme.mit.delta.java.mdd.MddNode;
import hu.bme.mit.delta.java.mdd.MddVariableHandle;
import hu.bme.mit.theta.analysis.algorithm.mdd.ansd.AbstractNextStateDescriptor;
import hu.bme.mit.theta.analysis.algorithm.mdd.ansd.StateSpaceInfo;
import java.util.Objects;

/**
 * The target-only (postcondition) descriptor of an MDD node, descending one level per key. The
 * descriptor reads its children through the {@link MddHandle}'s own {@link
 * hu.bme.mit.delta.collections.IntObjMapView} interpreter, so a bound presented over taller levels
 * added since it was built (a handle whose node sits below its variable handle) is floated down the
 * don't-care prefix automatically: the interpreter serves every value from the same node via a
 * default edge until the node's own level is reached.
 */
public class MddNodePostcondition implements AbstractNextStateDescriptor.Postcondition {

    private final MddHandle handle;

    private MddNodePostcondition(MddHandle handle) {
        this.handle = Preconditions.checkNotNull(handle);
    }

    public static AbstractNextStateDescriptor.Postcondition of(MddHandle handle) {
        final MddNode node = handle.getNode();
        final MddVariableHandle variableHandle = handle.getVariableHandle();
        if (node == null || node == variableHandle.getMddGraph().getTerminalZeroNode())
            return AbstractNextStateDescriptor.Postcondition.terminalEmpty();
        if (node.isTerminal() && !variableHandle.isTerminal()) {
            // a non-zero terminal above the bottom is a bound cut at the data boundary: accept below
            return AbstractNextStateDescriptor.Postcondition.acceptAll();
        }
        return new MddNodePostcondition(handle);
    }

    @Override
    public boolean evaluate() {
        return true;
    }

    @Override
    public IntObjMapView<AbstractNextStateDescriptor> getValuations(StateSpaceInfo localStateSpace) {
        return new IntObjMapViews.Transforming<>(handle, h -> of((MddHandle) h));
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;
        MddNodePostcondition that = (MddNodePostcondition) o;
        return Objects.equals(handle, that.handle);
    }

    @Override
    public int hashCode() {
        return Objects.hashCode(handle);
    }

    @Override
    public String toString() {
        return handle.toString();
    }
}
