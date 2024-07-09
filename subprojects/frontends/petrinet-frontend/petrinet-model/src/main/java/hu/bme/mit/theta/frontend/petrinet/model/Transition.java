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
package hu.bme.mit.theta.frontend.petrinet.model;

import java.util.ArrayList;
import java.util.List;

public final class Transition extends Identified {
    private List<TPArc> outgoingArcs = new ArrayList<>();
    private List<PTArc> incomingArcs = new ArrayList<>();

    public Transition(final String id) {
        super(id);
    }

    public List<TPArc> getOutgoingArcs() {
        return outgoingArcs;
    }

    public List<PTArc> getIncomingArcs() {
        return incomingArcs;
    }

    @Override
    public String toString() {
        return getId();
    }
}
