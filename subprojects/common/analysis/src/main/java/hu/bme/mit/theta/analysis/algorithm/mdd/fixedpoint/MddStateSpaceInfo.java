/*
 *  Copyright 2025-2026 Budapest University of Technology and Economics
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
package hu.bme.mit.theta.analysis.algorithm.mdd.fixedpoint;

import hu.bme.mit.delta.collections.IntSetView;
import hu.bme.mit.delta.collections.RecursiveIntObjMapView;
import hu.bme.mit.delta.java.mdd.MddNode;
import hu.bme.mit.delta.java.mdd.MddVariable;
import hu.bme.mit.theta.analysis.algorithm.mdd.ansd.StateSpaceInfo;

public final class MddStateSpaceInfo implements StateSpaceInfo {
    private final MddVariable variable;
    private final MddNode mddNode;

    public MddStateSpaceInfo(final MddVariable variable, final MddNode mddNode) {
        this.variable = variable;
        this.mddNode = mddNode;

        for (var c = mddNode.cursor(); c.moveNext(); ) {} // TODO delete later
    }

    @Override
    public Object getTraceInfo() {
        return variable.getTraceInfo();
    }

    // @Override
    // public ElementChain<Object> getComponentChain() {
    // 	class TraceInfoChain implements ElementChain<Object> {
    // 		private final MddVariableHandle mddVariableHandle;
    //
    // 		TraceInfoChain(MddVariableHandle mddVariableHandle) {
    // 			Preconditions.checkArgument(mddVariableHandle.getVariable().isPresent());
    // 			this.mddVariableHandle = mddVariableHandle;
    // 		}
    //
    // 		@Override
    // 		public Object getElement() {
    // 			return mddVariableHandle.getVariable().orElseThrow(AssertionError::new).getTraceInfo();
    // 		}
    //
    // 		@Override
    // 		public ElementChain<Object> next() {
    // 			if (mddVariableHandle.getLower().isPresent()) {
    // 				return new TraceInfoChain(mddVariableHandle.getLower().orElseThrow(AssertionError::new));
    // 			} else {
    // 				return null;
    // 			}
    // 		}
    // 	}
    //
    // 	return new TraceInfoChain(variableHandle);
    // }

    // TODO: else nodes are problematic, better not use them for now
    @Override
    public boolean hasInfiniteStates() {
        if (mddNode.isTerminal()) {
            return true;
        } else if (mddNode.isBelow(variable)) {
            return true;
        } else {
            return !variable.isNullOrZero(mddNode.defaultValue());
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
        // return null;
    }

    @Override
    public RecursiveIntObjMapView<?> toStructuralRepresentation() {
        var varHandle = variable.getDefaultSetSignatureHandle();
        var mddHandle = varHandle.getHandleFor(mddNode);
        return mddHandle;
    }
}
