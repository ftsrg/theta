package hu.bme.mit.theta.analysis.algorithm.symbolic.symbolicnode.expression;

import com.google.common.base.Preconditions;
import hu.bme.mit.delta.collections.IntObjMapView;
import hu.bme.mit.delta.collections.RecursiveIntObjCursor;
import hu.bme.mit.delta.collections.impl.IntObjMapViews;
import hu.bme.mit.delta.java.mdd.MddHandle;
import hu.bme.mit.theta.analysis.algorithm.symbolic.model.AbstractNextStateDescriptor;
import hu.bme.mit.theta.analysis.algorithm.symbolic.model.StateSpaceInfo;

public class MddNodeNextStateDescriptor implements AbstractNextStateDescriptor {

    private final MddHandle node;

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
        return new IntObjMapViews.Transforming<>(node, (n, key) -> {
            if(key == null) return AbstractNextStateDescriptor.terminalEmpty();
            else return MddNodeNextStateDescriptor.of((MddHandle) n.get(key));
        });
    }

    @Override
    public IntObjMapView<IntObjMapView<AbstractNextStateDescriptor>> getOffDiagonal(StateSpaceInfo localStateSpace) {
        return new IntObjMapViews.Transforming<>(node,
                outerNode -> new IntObjMapViews.Transforming<>(outerNode, n -> MddNodeNextStateDescriptor.of((MddHandle) n)));
    }

    @Override
    public AbstractNextStateDescriptor.Cursor rootCursor() {
        return new RootCursor(this);
    }

    public class Cursor implements AbstractNextStateDescriptor.Cursor {

        private final RecursiveIntObjCursor<? extends MddHandle> wrapped, fromCursor;

        private Cursor(RecursiveIntObjCursor<? extends MddHandle> wrapped, RecursiveIntObjCursor<? extends MddHandle> fromCursor){
            this.wrapped = wrapped;
            this.fromCursor = fromCursor;
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
            Preconditions.checkState(fromCursor.moveTo(from));
            return new Cursor(fromCursor.valueCursor(), fromCursor);
        }


        @Override
        public void close() {
            wrapped.close();
            fromCursor.close();
        }
    }

    public class RootCursor implements AbstractNextStateDescriptor.Cursor {

        private final MddNodeNextStateDescriptor descriptor;

        public RootCursor(MddNodeNextStateDescriptor descriptor) {
            this.descriptor = descriptor;
        }

        @Override
        public int key() {
            throw new UnsupportedOperationException("This operation is not supported on the root cursor");
        }

        @Override
        public AbstractNextStateDescriptor value() {
            return descriptor;
        }

        @Override
        public boolean moveNext() {
            throw new UnsupportedOperationException("This operation is not supported on the root cursor");
        }

        @Override
        public boolean moveTo(int key) {
            throw new UnsupportedOperationException("This operation is not supported on the root cursor");
        }

        @Override
        public AbstractNextStateDescriptor.Cursor valueCursor(int from) {
            var fromCursor = descriptor.node.cursor();
            Preconditions.checkState(fromCursor.moveTo(from));
            return new Cursor(fromCursor.valueCursor(), fromCursor);
        }

        @Override
        public void close() {}

    }
}
