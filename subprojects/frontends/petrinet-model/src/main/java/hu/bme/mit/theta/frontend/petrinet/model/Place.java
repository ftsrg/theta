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
package hu.bme.mit.theta.frontend.petrinet.model;

import java.util.ArrayList;
import java.util.List;

public final class Place extends Identified {
    private long initialMarking;

    private List<PTArc> outgoingArcs = new ArrayList<>();
    private List<TPArc> incomingArcs = new ArrayList<>();

    public Place(final String id) {
        super(id);
    }

    public long getInitialMarking() {
        return initialMarking;
    }

    public void setInitialMarking(final long initialMarking) {
        this.initialMarking = initialMarking;
    }

    public List<PTArc> getOutgoingArcs() {
        return outgoingArcs;
    }

    public List<TPArc> getIncomingArcs() {
        return incomingArcs;
    }

    @Override
    public String toString() {
        return getId();
    }
}
