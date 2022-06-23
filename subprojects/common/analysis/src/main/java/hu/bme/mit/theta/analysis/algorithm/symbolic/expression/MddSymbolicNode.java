package hu.bme.mit.theta.analysis.algorithm.symbolic.expression;

import com.google.common.base.Preconditions;
import com.koloboke.collect.map.hash.HashIntObjMap;
import com.koloboke.collect.map.hash.HashIntObjMaps;
import hu.bme.mit.delta.collections.IntObjMapView;
import hu.bme.mit.delta.java.DdLevel;
import hu.bme.mit.delta.java.mdd.MddNode;
import hu.bme.mit.delta.java.mdd.MddVariable;

public class MddSymbolicNode implements IMddSymbolicNode{

    private final Object symbolicRepresentation;
    private final MddVariable variable;

    // MddNodeból lopva
    private final DdLevel<MddNode> level;
    private final int              hashCode;
    private       int              references = 0;

    private final HashIntObjMap<MddSymbolicNode> cache;
    private MddSymbolicNode defaultValue;

    private boolean complete;

    public MddSymbolicNode(Object symbolicRepresentation, MddVariable variable, DdLevel<MddNode> level, int hashCode) {
        this.symbolicRepresentation = symbolicRepresentation;
        this.variable = variable;
        this.level = level;
        this.hashCode = hashCode;

        this.cache = HashIntObjMaps.newUpdatableMap();
        this.defaultValue = null;
        this.complete = false;
    }

    @Override
    public MddVariable getVariable() {
        return variable;
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

    public void cacheNode(int key, MddSymbolicNode node){
        Preconditions.checkState(!complete);
        this.cache.put(key, node);
    }

    public void cacheDefault(MddSymbolicNode defaultValue){
        Preconditions.checkState(!complete);
        this.defaultValue = defaultValue;
    }

    public void setComplete(){
        this.complete = true;
    }

    public IntObjMapView<MddSymbolicNode> getCacheView(){
        return IntObjMapView.of(cache, defaultValue);
    }

    public boolean isComplete(){
        return complete;
    }
}
