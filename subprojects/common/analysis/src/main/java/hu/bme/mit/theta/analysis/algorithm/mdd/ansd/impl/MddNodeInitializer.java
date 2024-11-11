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

public class MddNodeInitializer implements AbstractNextStateDescriptor.Postcondition {

    private final MddNode node;

    private final MddVariableHandle variableHandle;

    private MddNodeInitializer(final MddNode node, final MddVariableHandle variableHandle) {
        this.node = Preconditions.checkNotNull(node);
        this.variableHandle = Preconditions.checkNotNull(variableHandle);
        Preconditions.checkArgument(
                (variableHandle.isTerminal() && node.isTerminal())
                        || node.isOn(variableHandle.getVariable().orElseThrow()));
    }

    private static AbstractNextStateDescriptor.Postcondition of(
            final MddNode node, final MddVariableHandle variableHandle) {
        if (node == null || node == variableHandle.getMddGraph().getTerminalZeroNode()) {
            return AbstractNextStateDescriptor.Postcondition.terminalEmpty();
        } else {
            return new MddNodeInitializer(node, variableHandle);
        }
    }

    public static AbstractNextStateDescriptor.Postcondition of(final MddHandle handle) {
        return of(handle.getNode(), handle.getVariableHandle());
    }

    @Override
    public boolean evaluate() {
        return true;
    }

    @Override
    public IntObjMapView<AbstractNextStateDescriptor> getValuations(
            StateSpaceInfo localStateSpace) {
        return new IntObjMapViews.Transforming<>(
                node, n -> of(n, variableHandle.getLower().orElseThrow()));
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;
        MddNodeInitializer that = (MddNodeInitializer) o;
        return Objects.equals(node, that.node)
                && Objects.equals(variableHandle, that.variableHandle);
    }

    @Override
    public int hashCode() {
        return Objects.hash(node, variableHandle);
    }
}
