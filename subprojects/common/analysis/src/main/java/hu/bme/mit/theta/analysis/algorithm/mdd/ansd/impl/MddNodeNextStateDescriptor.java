/*
 *  Copyright 2026 Budapest University of Technology and Economics
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

import com.google.common.base.Preconditions;
import hu.bme.mit.delta.collections.IntObjCursor;
import hu.bme.mit.delta.collections.IntObjMapView;
import hu.bme.mit.delta.collections.RecursiveIntObjCursor;
import hu.bme.mit.delta.collections.RecursiveIntObjMapView;
import hu.bme.mit.delta.collections.impl.IntObjMapViews;
import hu.bme.mit.delta.java.mdd.MddHandle;
import hu.bme.mit.delta.java.mdd.MddNode;
import hu.bme.mit.delta.java.mdd.MddVariableHandle;
import hu.bme.mit.theta.analysis.algorithm.mdd.ansd.AbstractNextStateDescriptor;
import hu.bme.mit.theta.analysis.algorithm.mdd.ansd.StateSpaceInfo;
import hu.bme.mit.theta.analysis.algorithm.mdd.node.identity.IdentityRepresentation;
import java.util.List;
import java.util.Objects;
import java.util.Optional;

/**
 * The full-relation (source and target) descriptor of an MDD node, descending two levels per key.
 * The descriptor reads its children through the {@link MddHandle}'s own {@link
 * hu.bme.mit.delta.collections.IntObjMapView} interpreter, so a bound presented over taller levels
 * added since it was built (a handle whose node sits below its variable handle) is floated down the
 * don't-care prefix automatically: the interpreter serves every value from the same node via a
 * default edge until the node's own level is reached.
 */
public class MddNodeNextStateDescriptor implements AbstractNextStateDescriptor {

    private final MddHandle handle;

    private MddNodeNextStateDescriptor(MddHandle handle) {
        this.handle = Preconditions.checkNotNull(handle);
    }

    private static AbstractNextStateDescriptor of(MddNode node, MddVariableHandle variableHandle) {
        if (node == null || node == variableHandle.getMddGraph().getTerminalZeroNode())
            return AbstractNextStateDescriptor.terminalEmpty();
        return of(variableHandle.getHandleFor(node));
    }

    public static AbstractNextStateDescriptor of(MddHandle handle) {
        final MddNode node = handle.getNode();
        final MddVariableHandle variableHandle = handle.getVariableHandle();
        if (node == null || node == variableHandle.getMddGraph().getTerminalZeroNode())
            return AbstractNextStateDescriptor.terminalEmpty();
        if (node.isTerminal() && !variableHandle.isTerminal()) {
            // a non-zero terminal above the bottom is a bound cut at the data boundary: accept below
            return AbstractNextStateDescriptor.terminalIdentity();
        }
        if (node.getRepresentation()
                instanceof IdentityRepresentation identityExpressionRepresentation) {
            final var cont = identityExpressionRepresentation.getContinuation();
            return IdentityNextStateDescriptor.withChild(
                    MddNodeNextStateDescriptor.of(
                            cont,
                            variableHandle.getLower().orElseThrow().getLower().orElseThrow()));
        }
        return new MddNodeNextStateDescriptor(handle);
    }

    @Override
    public boolean evaluate() {
        return true;
    }

    @Override
    public IntObjMapView<AbstractNextStateDescriptor> getDiagonal(StateSpaceInfo localStateSpace) {
        final RecursiveIntObjMapView<?> constraint = localStateSpace.toStructuralRepresentation();
        // the handle indexes the source; on the diagonal the target equals the source, so the source
        // child is indexed by the same key — the interpreter floats both for a below-node, and an
        // absent source default yields the (empty) terminal so a real relation level still drives
        return new ConstrainedIntObjMapView<>(
                new IntObjMapViews.Transforming<>(
                        handle,
                        (source, key) -> {
                            final MddHandle sourceHandle = (MddHandle) source;
                            return of(key == null ? sourceHandle.defaultValue() : sourceHandle.get(key));
                        }),
                constraint);
    }

    @Override
    public IntObjMapView<IntObjMapView<AbstractNextStateDescriptor>> getOffDiagonal(
            StateSpaceInfo localStateSpace) {
        final RecursiveIntObjMapView<?> constraint = localStateSpace.toStructuralRepresentation();
        return new IntObjMapViews.Transforming<>(
                handle,
                outerSource -> {
                    final MddHandle sourceHandle = (MddHandle) outerSource;
                    return new ConstrainedIntObjMapView<>(
                            new IntObjMapViews.Transforming<>(
                                    sourceHandle, target -> of((MddHandle) target)),
                            constraint);
                });
    }

    @Override
    public AbstractNextStateDescriptor.Cursor rootCursor() {
        return new Cursor(
                RecursiveIntObjCursor.singleton(0, handle.getNode()), handle.getVariableHandle());
    }

    public class Cursor implements AbstractNextStateDescriptor.Cursor {
        private final RecursiveIntObjCursor<? extends MddNode> wrapped;

        private final MddVariableHandle variableHandle;

        private final Runnable closer;

        private Cursor(
                RecursiveIntObjCursor<? extends MddNode> wrapped,
                MddVariableHandle variableHandle,
                Runnable closer) {
            this.wrapped = wrapped;
            this.variableHandle = variableHandle;
            this.closer = closer;
        }

        private Cursor(
                RecursiveIntObjCursor<? extends MddNode> wrapped,
                MddVariableHandle variableHandle) {
            this(wrapped, variableHandle, () -> {});
        }

        @Override
        public int key() {
            return wrapped.key();
        }

        @Override
        public AbstractNextStateDescriptor value() {
            return MddNodeNextStateDescriptor.of(wrapped.value(), Cursor.this.variableHandle);
        }

        @Override
        public boolean moveNext() {
            return wrapped.moveNext();
        }

        @Override
        public boolean moveTo(int key) {
            return wrapped.moveTo(key);
        }

        @Override
        public AbstractNextStateDescriptor.Cursor valueCursor(
                int from, StateSpaceInfo localStateSpace) {
            // TODO the valueCursor call of the wrapped cursor has to propagate the constraint
            var fromCursor = wrapped.valueCursor();
            if (fromCursor.moveTo(from)) {
                return new Cursor(
                        fromCursor.valueCursor(),
                        Cursor.this
                                .variableHandle
                                .getLower()
                                .orElseThrow()
                                .getLower()
                                .orElseThrow(),
                        () -> fromCursor.close());
            } else return new EmptyCursor(() -> fromCursor.close());
        }

        @Override
        public void close() {
            wrapped.close();
            closer.run();
        }

        @Override
        public Optional<Iterable<AbstractNextStateDescriptor.Cursor>> split() {
            return Optional.of(List.of(this));
        }
    }

    public static class EmptyCursor implements AbstractNextStateDescriptor.Cursor {

        private final Runnable closer;

        public EmptyCursor(Runnable closer) {
            this.closer = closer;
        }

        @Override
        public int key() {
            throw new UnsupportedOperationException(
                    "This operation is not supported on the root cursor");
        }

        @Override
        public AbstractNextStateDescriptor value() {
            throw new UnsupportedOperationException(
                    "This operation is not supported on the root cursor");
        }

        @Override
        public boolean moveNext() {
            return false;
        }

        @Override
        public boolean moveTo(int key) {
            return false;
        }

        @Override
        public AbstractNextStateDescriptor.Cursor valueCursor(
                int from, StateSpaceInfo localStateSpace) {
            throw new UnsupportedOperationException(
                    "This operation is not supported on the root cursor");
        }

        @Override
        public void close() {
            this.closer.run();
        }

        @Override
        public Optional<Iterable<AbstractNextStateDescriptor.Cursor>> split() {
            return Optional.of(List.of(this));
        }
    }

    private class ConstrainedIntObjMapView<E> extends IntObjMapViews.ForwardingBase<E>
            implements IntObjMapView<E> {

        private final IntObjMapView<? extends E> target;
        private final IntObjMapView constraint;

        public ConstrainedIntObjMapView(
                IntObjMapView<? extends E> target, IntObjMapView constraint) {
            this.target = target;
            this.constraint = constraint;
        }

        @Override
        public IntObjMapView<? extends E> getForwardingTarget() {
            return this.target;
        }

        @Override
        public IntObjCursor<? extends E> cursor() {
            return target.cursor(constraint);
        }
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;
        MddNodeNextStateDescriptor that = (MddNodeNextStateDescriptor) o;
        return Objects.equals(handle, that.handle);
    }

    @Override
    public int hashCode() {
        return Objects.hashCode(handle);
    }

    @Override
    public String toString() {
        return handle.toString();
    }
}
