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

public final class PetriNet extends Identified {
    private String name;

    private List<Place> places = new ArrayList<>();
    private List<Transition> transitions = new ArrayList<>();
    private List<PTArc> ptArcs = new ArrayList<>();
    private List<TPArc> tpArcs = new ArrayList<>();

    public PetriNet(final String id) {
        super(id);
    }

    public String getName() {
        return name;
    }

    public void setName(final String name) {
        this.name = name;
    }

    public List<Place> getPlaces() {
        return places;
    }

    public List<Transition> getTransitions() {
        return transitions;
    }

    public List<PTArc> getPtArcs() {
        return ptArcs;
    }

    public List<TPArc> getTpArcs() {
        return tpArcs;
    }

    @Override
    public String toString() {
        return getId()
                + "("
                + places.size()
                + " places, "
                + transitions.size()
                + " transitions, "
                + (ptArcs.size() + tpArcs.size())
                + " arcs)";
    }
}
