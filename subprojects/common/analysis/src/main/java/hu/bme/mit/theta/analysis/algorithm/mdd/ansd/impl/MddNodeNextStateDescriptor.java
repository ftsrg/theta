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

import com.google.common.base.Preconditions;
import hu.bme.mit.delta.collections.IntObjCursor;
import hu.bme.mit.delta.collections.IntObjMapView;
import hu.bme.mit.delta.collections.RecursiveIntObjCursor;
import hu.bme.mit.delta.collections.impl.IntObjMapViews;
import hu.bme.mit.delta.java.mdd.MddHandle;
import hu.bme.mit.delta.java.mdd.MddNode;
import hu.bme.mit.delta.java.mdd.MddVariableHandle;
import hu.bme.mit.theta.analysis.algorithm.mdd.ansd.AbstractNextStateDescriptor;
import hu.bme.mit.theta.analysis.algorithm.mdd.ansd.StateSpaceInfo;
import hu.bme.mit.theta.analysis.algorithm.mdd.expressionnode.IdentityExpressionRepresentation;
import java.util.List;
import java.util.Objects;
import java.util.Optional;

public class MddNodeNextStateDescriptor implements AbstractNextStateDescriptor {

    private final MddNode node;

    private final MddVariableHandle variableHandle;

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;
        MddNodeNextStateDescriptor that = (MddNodeNextStateDescriptor) o;
        return Objects.equals(node, that.node)
                && Objects.equals(variableHandle, that.variableHandle);
    }

    @Override
    public int hashCode() {
        return Objects.hash(node, variableHandle);
    }

    @Override
    public String toString() {
        return node + ", " + variableHandle;
    }

    private MddNodeNextStateDescriptor(MddNode node, MddVariableHandle variableHandle) {
        this.node = Preconditions.checkNotNull(node);
        this.variableHandle = Preconditions.checkNotNull(variableHandle);
        Preconditions.checkArgument(
                (variableHandle.isTerminal() && node.isTerminal())
                        || node.isOn(variableHandle.getVariable().orElseThrow()));
    }

    private static AbstractNextStateDescriptor of(MddNode node, MddVariableHandle variableHandle) {
        if (node == null || node == variableHandle.getMddGraph().getTerminalZeroNode())
            return AbstractNextStateDescriptor.terminalEmpty();
        if (node.getRepresentation()
                instanceof IdentityExpressionRepresentation identityExpressionRepresentation) {
            final var cont = identityExpressionRepresentation.getContinuation();
            return IdentityNextStateDescriptor.withChild(
                    MddNodeNextStateDescriptor.of(
                            cont,
                            variableHandle.getLower().orElseThrow().getLower().orElseThrow()));
        }
        return new MddNodeNextStateDescriptor(node, variableHandle);
    }

    public static AbstractNextStateDescriptor of(MddHandle handle) {
        return of(handle.getNode(), handle.getVariableHandle());
    }

    @Override
    public boolean evaluate() {
        return true;
    }

    @Override
    public IntObjMapView<AbstractNextStateDescriptor> getDiagonal(StateSpaceInfo localStateSpace) {
        final MddNode constraint = localStateSpace.toStructuralRepresentation();
        return new ConstrainedIntObjMapView<>(
                new IntObjMapViews.Transforming<>(
                        node,
                        (n, key) -> {
                            if (key == null) return AbstractNextStateDescriptor.terminalEmpty();
                            else
                                return MddNodeNextStateDescriptor.of(
                                        n.get(key),
                                        variableHandle
                                                .getLower()
                                                .orElseThrow()
                                                .getLower()
                                                .orElseThrow());
                        }),
                constraint);
    }

    @Override
    public IntObjMapView<IntObjMapView<AbstractNextStateDescriptor>> getOffDiagonal(
            StateSpaceInfo localStateSpace) {
        final MddNode constraint = localStateSpace.toStructuralRepresentation();
        return new IntObjMapViews.Transforming<>(
                node,
                outerNode ->
                        new ConstrainedIntObjMapView<>(
                                new IntObjMapViews.Transforming<>(
                                        outerNode,
                                        mddNode ->
                                                MddNodeNextStateDescriptor.of(
                                                        mddNode,
                                                        variableHandle
                                                                .getLower()
                                                                .orElseThrow()
                                                                .getLower()
                                                                .orElseThrow())),
                                constraint));
    }

    @Override
    public AbstractNextStateDescriptor.Cursor rootCursor() {
        return new Cursor(RecursiveIntObjCursor.singleton(0, this.node), this.variableHandle);
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

        //        @Override
        //        public AbstractNextStateDescriptor.Cursor valueCursor(int from) {
        //            var fromCursor = wrapped.valueCursor();
        //            if (fromCursor.moveTo(from)) {
        //                return new Cursor(fromCursor.valueCursor(),
        // Cursor.this.variableHandle.getLower().orElseThrow().getLower().orElseThrow(), () ->
        // fromCursor.close());
        //            } else return new EmptyCursor(() -> fromCursor.close());
        //        }

        @Override
        public AbstractNextStateDescriptor.Cursor valueCursor(
                int from, StateSpaceInfo localStateSpace) {
            final MddNode constraint = localStateSpace.toStructuralRepresentation();
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

    //    public class Cursor extends CursorBase {
    //
    //        private final RecursiveIntObjCursor<? extends MddHandle> fromCursor;
    //
    //        private Cursor(RecursiveIntObjCursor<? extends MddHandle> wrapped,
    // RecursiveIntObjCursor<? extends MddHandle> fromCursor){
    //            super(wrapped);
    //            this.fromCursor = fromCursor;
    //        }
    //
    //        @Override
    //        public void close() {
    //            super.close();
    //            fromCursor.close();
    //        }
    //    }
    //
    //    public class RootCursor extends CursorBase {
    //
    //        private final MddNodeNextStateDescriptor descriptor;
    //
    //        private int currentPosition;
    //
    //        public RootCursor(MddNodeNextStateDescriptor descriptor) {
    //            super(descriptor.node.cursor());
    //            this.descriptor = descriptor;
    //            this.currentPosition = -1;
    //        }
    //
    //        @Override
    //        public int key() {
    //            throw new UnsupportedOperationException("This operation is not supported on the
    // root cursor");
    //        }
    //
    //        @Override
    //        public AbstractNextStateDescriptor value() {
    //            return descriptor;
    //        }
    //
    //        @Override
    //        public boolean moveNext() {
    //            currentPosition++;
    //            return currentPosition == 0;
    //        }
    //
    //        @Override
    //        public boolean moveTo(int key) {
    //            throw new UnsupportedOperationException("This operation is not supported on the
    // root cursor");
    //        }
    //
    //        @Override
    //        public AbstractNextStateDescriptor.Cursor valueCursor(int from) {
    //            var fromCursor = descriptor.node.cursor();
    //            if(fromCursor.moveTo(from)) {
    //                return new Cursor(fromCursor.valueCursor(), fromCursor);
    //            } else {
    //                return EmptyCursor.INSTANCE;
    //            }
    //
    //        }
    //
    //        @Override
    //        public void close() {}
    //
    //    }

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
}
