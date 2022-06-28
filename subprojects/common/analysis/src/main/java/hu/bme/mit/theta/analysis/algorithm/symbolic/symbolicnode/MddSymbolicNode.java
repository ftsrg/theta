package hu.bme.mit.theta.analysis.algorithm.symbolic.symbolicnode;

import com.google.common.base.Preconditions;
import hu.bme.mit.delta.Pair;
import hu.bme.mit.delta.collections.IntObjMapView;
import hu.bme.mit.delta.java.DdLevel;
import hu.bme.mit.delta.java.mdd.MddNode;
import hu.bme.mit.delta.java.mdd.MddVariable;

public class MddSymbolicNode implements IMddSymbolicNode {

    private final Pair<Object, MddVariable> symbolicRepresentation;

    // MddNodeból lopva
    private final DdLevel<MddNode> level;
    private final int hashCode;
    private int references = 0;

    private final MddSymbolicNodeTraverser.ExplicitRepresentation explicitRepresentation;

    public MddSymbolicNode(Pair<Object, MddVariable> symbolicRepresentation, DdLevel<MddNode> level) {
        this.symbolicRepresentation = symbolicRepresentation;
        this.level = level;
        this.hashCode = symbolicRepresentation.hashCode();

        this.explicitRepresentation = new MddSymbolicNodeTraverser.ExplicitRepresentation();
    }

    public MddVariable getVariable() {
        return symbolicRepresentation.second;
    }

    @Override
    public Object getSymbolicRepresentation() {
        return symbolicRepresentation;
    }

    @Override
    public int hashCode() {
        return hashCode;
    }

    @Override
    public boolean isOn(MddVariable variable) {
        Preconditions.checkNotNull(variable, "variable");
        return this.level == variable.getLevel();
    }

    @Override
    public boolean isAbove(MddVariable variable) {
        Preconditions.checkNotNull(variable, "variable");
        return this.level.isAbove(variable.getLevel());
    }

    @Override
    public boolean isBelow(MddVariable variable) {
        Preconditions.checkNotNull(variable, "variable");
        return this.level.isBelow(variable.getLevel());
    }

    @Override
    public void acquire() {
        if (references == 0) {
            acquireChildren();
        }
        references++;
    }

    private void acquireChildren() {
        // Ez így biztos nem lesz jó
//        for (IntObjCursor<? extends MddNode> c = this.cursor(); c.moveNext(); ) {
//            c.value().acquire();
//        }
//        if ((this.defaultValue() != null) && (this.defaultValue() != this)) {
//            this.defaultValue().acquire();
//        }
    }

    @Override
    public void release() {
        Preconditions.checkArgument(references > 0, "Invalid release on MDD node.");
        references--;
        if (references == 0) {
            releaseChildren();
        }
    }

    private void releaseChildren() {
//        for (IntObjCursor<? extends MddNode> c = this.cursor(); c.moveNext(); ) {
//            c.value().release();
//        }
//        if ((this.defaultValue() != null) && (this.defaultValue() != this)) {
//            this.defaultValue().release();
//        }
    }

    @Override
    public int getReferenceCount() {
        return references;
    }

    public MddSymbolicNodeTraverser.ExplicitRepresentation getExplicitRepresentation() {
        return explicitRepresentation;
    }

    public IntObjMapView<MddSymbolicNode> getCacheView() {
        return explicitRepresentation.getCacheView();
    }

    public boolean isComplete() {
        return explicitRepresentation.isComplete();
    }
}
