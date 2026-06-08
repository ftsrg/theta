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
package hu.bme.mit.theta.analysis.algorithm.mdd.ansd.impl;

import hu.bme.mit.delta.collections.IntObjMapView;
import hu.bme.mit.delta.collections.PrototypedUniqueTable;
import hu.bme.mit.theta.analysis.algorithm.mdd.ansd.AbstractNextStateDescriptor;
import hu.bme.mit.theta.analysis.algorithm.mdd.ansd.StateSpaceInfo;
import java.util.Objects;
import java.util.Optional;

public final class IdentityNextStateDescriptor implements AbstractNextStateDescriptor {
    private final AbstractNextStateDescriptor child;
    private final int cachedHash;

    private static final PrototypedUniqueTable<IdentityNextStateDescriptor> UNIQUE_TABLE =
            PrototypedUniqueTable.newInstance();

    public static final AbstractNextStateDescriptor TERMINAL_IDENTITY =
            new IdentityNextStateDescriptor();

    public static AbstractNextStateDescriptor withChild(final AbstractNextStateDescriptor child) {
        final Template proto = new Template(child);
        return UNIQUE_TABLE.checkIn(proto, t -> new IdentityNextStateDescriptor(t.child));
    }

    private IdentityNextStateDescriptor() {
        this.child = this;
        this.cachedHash = Objects.hashCode(child);
    }

    private IdentityNextStateDescriptor(final AbstractNextStateDescriptor child) {
        this.child = child;
        this.cachedHash = Objects.hashCode(child);
    }

    @Override
    public boolean equals(final Object obj) {
        return this == obj;
    }

    @Override
    public int hashCode() {
        return cachedHash;
    }

    @Override
    public IntObjMapView<AbstractNextStateDescriptor> getDiagonal(
            final StateSpaceInfo localStateSpace) {
        return IntObjMapView.empty(child);
    }

    @Override
    public IntObjMapView<IntObjMapView<AbstractNextStateDescriptor>> getOffDiagonal(
            final StateSpaceInfo localStateSpace) {
        return IntObjMapView.empty(
                IntObjMapView.empty(AbstractNextStateDescriptor.terminalEmpty()));
    }

    @Override
    public Optional<Iterable<AbstractNextStateDescriptor>> split() {
        return Optional.empty();
    }

    @Override
    public boolean evaluate() {
        return true;
    }

    private static final class Template {

        private final AbstractNextStateDescriptor child;

        private Template(final AbstractNextStateDescriptor child) {
            this.child = child;
        }

        @Override
        public boolean equals(final Object obj) {
            if (this == obj) return true;
            if (obj instanceof Template other) {
                return Objects.equals(this.child, other.child);
            }
            if (obj instanceof IdentityNextStateDescriptor descriptor) {
                return Objects.equals(this.child, descriptor.child);
            }
            return false;
        }

        @Override
        public int hashCode() {
            return Objects.hashCode(child);
        }
    }
}
