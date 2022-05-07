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
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.xcfa.model.XcfaLabel;

import java.util.ArrayList;
import java.util.Collection;
import java.util.LinkedHashMap;
import java.util.Map;

public class XcfaProcessMemEventProvider implements MemoryEventProvider<XcfaProcessAction> {
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
    public Collection<MemoryEvent> getMemoryEventsOf(XcfaProcessAction action) {
        final Collection<MemoryEvent> memoryEvents = new ArrayList<>();
        for (final XcfaLabel label : action.getEdge().getLabels()) {
            collectMemoryEvents(memoryEvents, label);
        }
        return memoryEvents;
    }

    private void collectMemoryEvents(Collection<MemoryEvent> memoryEvents, XcfaLabel label) {
        if(label instanceof XcfaLabel.StoreXcfaLabel<?>) {
            VarDecl<?> global = ((XcfaLabel.StoreXcfaLabel<?>) label).getGlobal();
            memoryEvents.add(new MemoryEvent(getId(global), global, MemoryEvent.MemoryEventType.WRITE));
        } else if (label instanceof XcfaLabel.LoadXcfaLabel<?>) {
            VarDecl<?> global = ((XcfaLabel.LoadXcfaLabel<?>) label).getGlobal();
            memoryEvents.add(new MemoryEvent(getId(global), global, MemoryEvent.MemoryEventType.READ));
        } else if (label instanceof XcfaLabel.FenceXcfaLabel) {
            memoryEvents.add(new MemoryEvent(0, null, MemoryEvent.MemoryEventType.FENCE));
        } else if (label instanceof XcfaLabel.SequenceLabel) {
            for (XcfaLabel xcfaLabel : ((XcfaLabel.SequenceLabel) label).getLabels()) {
                collectMemoryEvents(memoryEvents, xcfaLabel);
            }
        }
    }
}
