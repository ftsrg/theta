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
package hu.bme.mit.theta.sts.aiger.elements;

import java.util.Collection;

/** Base class for nodes in an {@link AigerSystem}. */
public abstract class AigerNode {

    private final String name;

    public AigerNode(final String name) {
        this.name = name;
    }

    public String getName() {
        return name;
    }

    public abstract Collection<AigerWire> getInWires();

    public abstract Collection<AigerWire> getOutWires();

    public abstract void addOutWire(AigerWire outWire);

    // public abstract void removeOutWire(AigerWire outWire);
}
