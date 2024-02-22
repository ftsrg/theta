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

import hu.bme.mit.delta.collections.ElementChain;
import hu.bme.mit.delta.collections.IntSetView;
import hu.bme.mit.delta.java.mdd.MddNode;
import hu.bme.mit.delta.java.mdd.MddVariableHandle;
import hu.bme.mit.theta.analysis.algorithm.symbolic.model.StateSpaceInfo;

import java.util.Objects;

public class DomainBasedStateSpaceInfo implements StateSpaceInfo {
    private final ElementChain<Object> componentChain;
    private final MddVariableHandle variableHandle;
    private final MddNode mddNode;

    public DomainBasedStateSpaceInfo(ElementChain<Object> componentChain, MddVariableHandle variableHandle,
                                     MddNode mddNode) {
        this.componentChain = componentChain;
        this.variableHandle = variableHandle;
        this.mddNode = mddNode;
    }

    // @Override
    // public ElementChain<Object> getComponentChain() {
    // 	return componentChain;
    // }

    @Override
    public Object getTraceInfo() {
        return variableHandle.getVariable().orElseThrow(AssertionError::new).getTraceInfo();
    }

    @Override
    public boolean hasInfiniteStates() {
        if (mddNode.isTerminal()) {
            // Certainly level skip
            return true;
        } else if (mddNode.isBelow(variableHandle.getVariable().orElseThrow(AssertionError::new))) {
            // Level skip
            return true;
        } else {
            // Default value is specified
            return !variableHandle.getVariable().orElseThrow(AssertionError::new).isNullOrZero(mddNode.defaultValue());
        }
    }

    @Override
    public IntSetView getLocalStateSpace() {
        return mddNode.keySet();
    }

    @Override
    public StateSpaceInfo getLocalStateSpace(final Object someLowerComponent) {
        // TODO: Auto-generated method stub.
        throw new UnsupportedOperationException("Not (yet) implemented.");
        //return null;
    }

    @Override
    public MddNode toStructuralRepresentation() {

        return null;
    }

    @Override
    public boolean equals(Object obj) {
        if (obj instanceof DomainBasedStateSpaceInfo) {
            DomainBasedStateSpaceInfo other = (DomainBasedStateSpaceInfo) obj;
            return mddNode.equals(other.mddNode) && componentChain.equals(other.componentChain);
        }
        return false;
    }

    @Override
    public int hashCode() {
        return Objects.hash(componentChain, mddNode);
    }
}
