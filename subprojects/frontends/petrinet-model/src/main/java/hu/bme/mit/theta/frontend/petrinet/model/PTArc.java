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

public final class PTArc extends Identified {
    private boolean isInhibitor;
    private long weight;

    private Place source;
    private Transition target;

    public PTArc(final String id) {
        super(id);
    }

    public boolean isInhibitor() {
        return isInhibitor;
    }

    public void setInhibitor(final boolean inhibitor) {
        isInhibitor = inhibitor;
    }

    public long getWeight() {
        return weight;
    }

    public void setWeight(final long weight) {
        this.weight = weight;
    }

    public Place getSource() {
        return source;
    }

    public void setSource(final Place source) {
        if (this.source != null) {
            this.source.getOutgoingArcs().remove(this);
        }
        this.source = source;
        if (this.source != null) {
            this.source.getOutgoingArcs().add(this);
        }
    }

    public Transition getTarget() {
        return target;
    }

    public void setTarget(final Transition target) {
        if (this.target != null) {
            this.target.getIncomingArcs().remove(this);
        }
        this.target = target;
        if (this.target != null) {
            this.target.getIncomingArcs().add(this);
        }
    }

    @Override
    public String toString() {
        return getId() + " (" + source.toString() + "->" + target.toString() + ")";
    }
}
