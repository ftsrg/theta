package hu.bme.mit.theta.analysis.algorithm.symbolic.symbolicnode.expression;

import hu.bme.mit.delta.collections.IntObjMapView;
import hu.bme.mit.delta.collections.RecursiveIntObjCursor;
import hu.bme.mit.delta.collections.impl.IntObjMapViews;
import hu.bme.mit.delta.java.mdd.MddHandle;
import hu.bme.mit.theta.analysis.algorithm.symbolic.model.AbstractNextStateDescriptor;
import hu.bme.mit.theta.analysis.algorithm.symbolic.model.RecursiveAbstractNextStateDescriptor;
import hu.bme.mit.theta.analysis.algorithm.symbolic.model.StateSpaceInfo;
import hu.bme.mit.theta.analysis.algorithm.symbolic.model.impl.EmptyNextStateDescriptor;

public class MddNodeNextStateDescriptor implements RecursiveAbstractNextStateDescriptor {

    private final MddHandle node;

    private MddNodeNextStateDescriptor(MddHandle node) {
        this.node = node;
    }

    public static RecursiveAbstractNextStateDescriptor of(MddHandle node){
        return node.isTerminalZero() ? EmptyNextStateDescriptor.INSTANCE : new MddNodeNextStateDescriptor(node);
    }

    @Override
    public boolean evaluate() {
        return !node.isTerminalZero();
    }

    @Override
    public IntObjMapView<AbstractNextStateDescriptor> getDiagonal(StateSpaceInfo localStateSpace) {
        return new IntObjMapViews.Transforming<>(node, (n, key) -> {
            if(key == null) return EmptyNextStateDescriptor.INSTANCE;
            else return MddNodeNextStateDescriptor.of((MddHandle) n.get(key));
        });
    }

    @Override
    public IntObjMapView<IntObjMapView<AbstractNextStateDescriptor>> getOffDiagonal(StateSpaceInfo localStateSpace) {
        return new IntObjMapViews.Transforming<>(node,
                outerNode -> new IntObjMapViews.Transforming<>(outerNode, n -> MddNodeNextStateDescriptor.of((MddHandle) n)));
    }

    @Override
    public RecursiveAbstractNextStateDescriptor.Cursor cursor(int from) {
        return new Cursor(node.cursor());
    }

    public static class Cursor implements RecursiveAbstractNextStateDescriptor.Cursor {

        private final RecursiveIntObjCursor<? extends MddHandle> wrapped, fromCursor;

        public Cursor(RecursiveIntObjCursor<? extends MddHandle> wrapped){
            this.wrapped = wrapped;
            this.fromCursor = null;
        }

        public Cursor(RecursiveIntObjCursor<? extends MddHandle> wrapped, RecursiveIntObjCursor<? extends MddHandle> fromCursor){
            this.wrapped = wrapped;
            this.fromCursor = fromCursor;
        }

        @Override
        public int key() {
            return wrapped.key();
        }

        @Override
        public RecursiveAbstractNextStateDescriptor value() {
            return MddNodeNextStateDescriptor.of(wrapped.value());
        }

        @Override
        public boolean moveNext() {
            return wrapped.moveNext();
        }

        @Override
        public RecursiveAbstractNextStateDescriptor.Cursor valueCursor(int from) {
            var fromCursor = wrapped.valueCursor();
            fromCursor.moveTo(from);
            return new Cursor(fromCursor.valueCursor(), fromCursor);
        }


        @Override
        public void close() {
            wrapped.close();
            if(fromCursor != null) fromCursor.close();
        }
    }
}
