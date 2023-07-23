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

package hu.bme.mit.theta.analysis.algorithm.mcm.mcm;

import hu.bme.mit.theta.core.decl.VarDecl;

import java.util.Set;

public class MemoryEvent {
    protected final MemoryEventType type;
    protected final String tag;
    protected final int id;

    public MemoryEvent(MemoryEventType type, String tag, int id) {
        this.type = type;
        this.tag = tag;
        this.id = id;
    }

    public String tag() {
        return tag;
    }

    public enum MemoryEventType {
        READ("R"),
        WRITE("W"),
        FENCE("F"),
        META("M");

        public final String label;

        private MemoryEventType(String label) {
            this.label = label;
        }
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
        private final VarDecl<?> var;
        private final VarDecl<?> localVar;

        public MemoryIO(int id, VarDecl<?> var, VarDecl<?> localVar, MemoryEventType type, String tag) {
            super(type, tag, id);
            this.var = var;
            this.localVar = localVar;
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
                    ", id=" + id +
                    '}';
        }

        public VarDecl<?> var() {
            return var;
        }

        public VarDecl<?> localVar() {
            return localVar;
        }

    }

    public static final class Read extends MemoryIO {
        public Read(int id, VarDecl<?> var, VarDecl<?> localVar, String tag) {
            super(id, var, localVar, MemoryEventType.READ, tag);
        }

        @Override
        public Read asRead() {
            return this;
        }
    }

    public static final class Write extends MemoryIO {
        private final Set<VarDecl<?>> dependencies;

        public Write(int id, VarDecl<?> var, VarDecl<?> localVar, Set<VarDecl<?>> dependencies, String tag) {
            super(id, var, localVar, MemoryEventType.WRITE, tag);
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

    public static final class Fence extends MemoryEvent {
        public Fence(int id, String tag) {
            super(MemoryEventType.FENCE, tag, id);
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
