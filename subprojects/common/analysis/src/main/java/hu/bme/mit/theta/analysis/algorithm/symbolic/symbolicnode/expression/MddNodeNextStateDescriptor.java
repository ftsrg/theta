package hu.bme.mit.theta.analysis.algorithm.symbolic.symbolicnode.expression;

import hu.bme.mit.delta.collections.IntObjCursor;
import hu.bme.mit.delta.collections.IntObjMapView;
import hu.bme.mit.delta.collections.RecursiveIntObjCursor;
import hu.bme.mit.delta.collections.impl.IntObjMapViews;
import hu.bme.mit.delta.java.mdd.MddHandle;
import hu.bme.mit.delta.java.mdd.MddNode;
import hu.bme.mit.theta.analysis.algorithm.symbolic.model.AbstractNextStateDescriptor;
import hu.bme.mit.theta.analysis.algorithm.symbolic.model.StateSpaceInfo;

import java.util.List;
import java.util.Objects;
import java.util.Optional;

public class MddNodeNextStateDescriptor implements AbstractNextStateDescriptor {

    private final MddHandle node;

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;
        MddNodeNextStateDescriptor that = (MddNodeNextStateDescriptor) o;
        return Objects.equals(node, that.node);
    }

    @Override
    public int hashCode() {
        return Objects.hash(node);
    }

    private MddNodeNextStateDescriptor(MddHandle node) {
        this.node = node;
    }

    public static AbstractNextStateDescriptor of(MddHandle node){
        return node.isTerminalZero() ? AbstractNextStateDescriptor.terminalEmpty() : new MddNodeNextStateDescriptor(node);
    }

    @Override
    public boolean evaluate() {
        return !node.isTerminalZero();
    }

    @Override
    public IntObjMapView<AbstractNextStateDescriptor> getDiagonal(StateSpaceInfo localStateSpace) {
        final MddNode constraint = localStateSpace.toStructuralRepresentation();
        return new ConstrainedIntObjMapView<>(new IntObjMapViews.Transforming<>(node, (n, key) -> {
            if(key == null) return AbstractNextStateDescriptor.terminalEmpty();
            else return MddNodeNextStateDescriptor.of((MddHandle) n.get(key));
        }), constraint);
    }

    @Override
    public IntObjMapView<IntObjMapView<AbstractNextStateDescriptor>> getOffDiagonal(StateSpaceInfo localStateSpace) {
        final MddNode constraint = localStateSpace.toStructuralRepresentation();
        return new IntObjMapViews.Transforming<>(node,
                outerNode -> new ConstrainedIntObjMapView<>(new IntObjMapViews.Transforming<>(outerNode, n -> MddNodeNextStateDescriptor.of((MddHandle) n)),constraint));
    }

    @Override
    public AbstractNextStateDescriptor.Cursor rootCursor() {
        return new Cursor(RecursiveIntObjCursor.singleton(0, this.node));
    }

    public static class Cursor implements AbstractNextStateDescriptor.Cursor {
        private final RecursiveIntObjCursor<? extends MddHandle> wrapped;

        private final Runnable closer;

        private Cursor(RecursiveIntObjCursor<? extends MddHandle> wrapped, Runnable closer){
            this.wrapped = wrapped;
            this.closer = closer;
        }

        private Cursor(RecursiveIntObjCursor<? extends MddHandle> wrapped){
            this.wrapped = wrapped;
            this.closer = () -> {};
        }

        @Override
        public int key() {
            return wrapped.key();
        }

        @Override
        public AbstractNextStateDescriptor value() {
            return MddNodeNextStateDescriptor.of(wrapped.value());
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
        public AbstractNextStateDescriptor.Cursor valueCursor(int from) {
            var fromCursor = wrapped.valueCursor();
            if (fromCursor.moveTo(from)) {
                return new Cursor(fromCursor.valueCursor(), () -> fromCursor.close());
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
//        private Cursor(RecursiveIntObjCursor<? extends MddHandle> wrapped, RecursiveIntObjCursor<? extends MddHandle> fromCursor){
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
//            throw new UnsupportedOperationException("This operation is not supported on the root cursor");
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
//            throw new UnsupportedOperationException("This operation is not supported on the root cursor");
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
            throw new UnsupportedOperationException("This operation is not supported on the root cursor");
        }

        @Override
        public AbstractNextStateDescriptor value() {
            throw new UnsupportedOperationException("This operation is not supported on the root cursor");
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
        public AbstractNextStateDescriptor.Cursor valueCursor(int from) {
            throw new UnsupportedOperationException("This operation is not supported on the root cursor");
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

    private class ConstrainedIntObjMapView<E> extends IntObjMapViews.ForwardingBase<E> implements IntObjMapView<E> {

        private final IntObjMapView<? extends E> target;
        private final IntObjMapView constraint;

        public ConstrainedIntObjMapView(IntObjMapView<? extends E> target, IntObjMapView constraint) {
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
