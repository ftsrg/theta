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

package hu.bme.mit.theta.analysis.algorithm.mcm;

import hu.bme.mit.theta.core.decl.VarDecl;

import static com.google.common.base.Preconditions.checkArgument;

public class MemoryEvent {
    private final int varId;
    private final VarDecl<?> var;
    private final MemoryEventType type;

    public MemoryEvent(int varId, VarDecl<?> var, MemoryEventType type) {
        this.var = var;
        checkArgument(varId <= 0, "Meta event IDs must be negative!");
        this.varId = varId;
        this.type = type;
    }

    public int getVarId() {
        return varId;
    }

    public MemoryEventType getType() {
        return type;
    }

    public VarDecl<?> getVar() {
        return var;
    }

    public enum MemoryEventType {
        READ,
        WRITE,
        FENCE
    }
}
