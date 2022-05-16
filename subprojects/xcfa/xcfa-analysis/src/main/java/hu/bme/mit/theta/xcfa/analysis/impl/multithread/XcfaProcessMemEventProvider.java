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

import hu.bme.mit.theta.analysis.algorithm.mcm.MemoryEvent;
import hu.bme.mit.theta.analysis.algorithm.mcm.MemoryEventProvider;
import hu.bme.mit.theta.analysis.expr.ExprState;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.xcfa.model.XcfaEdge;
import hu.bme.mit.theta.xcfa.model.XcfaLabel;
import hu.bme.mit.theta.xcfa.model.XcfaLocation;

import java.util.*;
public class XcfaProcessMemEventProvider<S extends ExprState> implements MemoryEventProvider<XcfaProcessState<S>, XcfaProcessAction> {
    private final Map<VarDecl<?>, Integer> varIdLookup;
    private final int idOffset;

    public XcfaProcessMemEventProvider(final int idOffset) {
        this.idOffset = idOffset;
        varIdLookup = new LinkedHashMap<>();
    }

    private int getId(VarDecl<?> varDecl) {
        if(!varIdLookup.containsKey(varDecl)) {
            varIdLookup.put(varDecl, (varIdLookup.size() + 1 + idOffset) * -1);
        }
        return varIdLookup.get(varDecl);
    }

    @Override
    public Collection<ResultElement<XcfaProcessAction>> getPiecewiseAction(XcfaProcessState<S> state, XcfaProcessAction action) {
        final Collection<ResultElement<XcfaProcessAction>> ret = new ArrayList<>();
        Map<VarDecl<?>, Set<VarDecl<?>>> dependencies = new LinkedHashMap<>(state.getDependencies());
        XcfaEdge edge = action.getEdge();
        for (final XcfaLabel label : edge.getLabels()) {
            collectPieces(ret, label, dependencies, edge.getSource());
        }
        if(edge.getTarget().isEndLoc()) {
            ret.add(new ResultElement<>(new MemoryEvent.Fence("thread-end")));
        }
        ret.add(new ResultElement<>(new XcfaProcessAction(edge.withLabels(List.of()))));
        return ret;
    }

    @Override
    public int getVarId(VarDecl<?> var) {
        return getId(var);
    }

    private void collectPieces(Collection<ResultElement<XcfaProcessAction>> ret, XcfaLabel label, Map<VarDecl<?>, Set<VarDecl<?>>> dependencies, XcfaLocation source) {
        if(label instanceof XcfaLabel.StoreXcfaLabel<?>) {
            VarDecl<?> global = ((XcfaLabel.StoreXcfaLabel<?>) label).getGlobal();
            VarDecl<?> local = ((XcfaLabel.StoreXcfaLabel<?>) label).getLocal();
            ret.add(new ResultElement<>(new MemoryEvent.Write(getId(global), global, local, dependencies.get(local), ((XcfaLabel.StoreXcfaLabel<?>) label).getOrdering())));
        } else if (label instanceof XcfaLabel.LoadXcfaLabel<?>) {
            VarDecl<?> global = ((XcfaLabel.LoadXcfaLabel<?>) label).getGlobal();
            VarDecl<?> local = ((XcfaLabel.LoadXcfaLabel<?>) label).getLocal();
            ret.add(new ResultElement<>(new MemoryEvent.Read(getId(global), global, local, ((XcfaLabel.LoadXcfaLabel<?>) label).getOrdering())));
        } else if (label instanceof XcfaLabel.FenceXcfaLabel) {
            ret.add(new ResultElement<>(new MemoryEvent.Fence(((XcfaLabel.FenceXcfaLabel) label).getType())));
        } else if (label instanceof XcfaLabel.SequenceLabel) {
            for (XcfaLabel xcfaLabel : ((XcfaLabel.SequenceLabel) label).getLabels()) {
                collectPieces(ret, xcfaLabel, dependencies, source);
            }
        } else {
            ret.add(new ResultElement<>(new XcfaProcessAction(XcfaEdge.of(source, source, List.of(label)))));
        }
        label.accept(new XcfaLabelDependencyCollector(), dependencies);
    }
}
