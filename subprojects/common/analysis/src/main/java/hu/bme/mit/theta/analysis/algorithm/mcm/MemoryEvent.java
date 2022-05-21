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

import java.util.Set;

import static com.google.common.base.Preconditions.checkArgument;

public class MemoryEvent {
    protected final MemoryEventType type;
    protected final String tag;

    public MemoryEvent(MemoryEventType type, String tag) {
        this.type = type;
        this.tag = tag;
    }

    public String tag() {
        return tag;
    }

    public enum MemoryEventType {
        READ,
        WRITE,
        FENCE,
        META
    }

    public MemoryEventType type() {
        return type;
    }

    public Read asRead() {
        throw new UnsupportedOperationException("Not a read!");
    }
    public Write asWrite() {
        throw new UnsupportedOperationException("Not a write!");
    }
    public Fence asFence() {
        throw new UnsupportedOperationException("Not a fence!");
    }
    public MemoryIO asMemoryIO() {
        throw new UnsupportedOperationException("Not memory IO!");
    }

    public static abstract class MemoryIO extends MemoryEvent {
        private final int varId;
        private final VarDecl<?> var;
        private final VarDecl<?> localVar;
        public MemoryIO(int varId, VarDecl<?> var, VarDecl<?> localVar, MemoryEventType type, String tag) {
            super(type, tag);
            checkArgument(varId <= 0, "Meta event IDs must be negative!");
            this.var = var;
            this.localVar = localVar;
            this.varId = varId;
        }

        @Override
        public MemoryIO asMemoryIO() {
            return this;
        }

        @Override
        public String toString() {
            return type + "{" +
                    "var=" + var +
                    ", localVar=" + localVar +
                    ", tag=" + tag +
                    '}';
        }

        public int varId() {
            return varId;
        }

        public VarDecl<?> var() {
            return var;
        }

        public VarDecl<?> localVar() {
            return localVar;
        }

    }

    public static final class Read extends MemoryIO{
        public Read(int varId, VarDecl<?> var, VarDecl<?> localVar, String tag) {
            super(varId, var, localVar, MemoryEventType.READ, tag);
        }

        @Override
        public Read asRead() {
            return this;
        }
    }
    public static final class Write extends MemoryIO{
        private final Set<VarDecl<?>> dependencies;
        public Write(int varId, VarDecl<?> var, VarDecl<?> localVar, Set<VarDecl<?>> dependencies, String tag) {
            super(varId, var, localVar, MemoryEventType.WRITE, tag);
            this.dependencies = dependencies;
        }

        @Override
        public Write asWrite() {
            return this;
        }

        public Set<VarDecl<?>> dependencies() {
            return dependencies;
        }
    }
    public static final class Fence extends MemoryEvent{
        public Fence(String tag) {
            super(MemoryEventType.FENCE, tag);
        }

        @Override
        public Fence asFence() {
            return this;
        }

        @Override
        public String toString() {
            return type + "{" +
                    "tag='" + tag + '\'' +
                    '}';
        }
    }

}
