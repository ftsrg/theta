/*
 *  Copyright 2023 Budapest University of Technology and Economics
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
package hu.bme.mit.theta.xsts.pnml.elements;

import java.util.ArrayList;
import java.util.Collection;

public abstract class PnmlNode {

    private final String name;
    private final String id;
    private final Collection<PnmlArc> inArcs;
    private final Collection<PnmlArc> outArcs;

    protected PnmlNode(final String name, final String id) {
        this.name = name;
        this.id = id;
        this.inArcs = new ArrayList<>();
        this.outArcs = new ArrayList<>();
    }

    public String getName() {
        return name;
    }

    public String getId() {
        return id;
    }

    public void addInArc(final PnmlArc inArc) {
        inArcs.add(inArc);
    }

    public void addOutArc(final PnmlArc outArc) {
        outArcs.add(outArc);
    }

    public Collection<PnmlArc> getInArcs() {
        return inArcs;
    }

    public Collection<PnmlArc> getOutArcs() {
        return outArcs;
    }

}
