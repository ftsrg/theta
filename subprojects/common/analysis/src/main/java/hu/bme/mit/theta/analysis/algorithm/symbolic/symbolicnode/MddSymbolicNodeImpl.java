package hu.bme.mit.theta.analysis.algorithm.symbolic.symbolicnode;

import com.google.common.base.Preconditions;
import com.koloboke.collect.map.hash.HashIntObjMap;
import com.koloboke.collect.map.hash.HashIntObjMaps;
import hu.bme.mit.delta.Pair;
import hu.bme.mit.delta.collections.IntObjMapView;
import hu.bme.mit.delta.java.DdLevel;
import hu.bme.mit.delta.java.mdd.MddNode;
import hu.bme.mit.delta.java.mdd.MddVariable;
import hu.bme.mit.theta.common.GrowingIntArray;

import java.util.Objects;

/**
 * Represents a decision that is encoded in a symbolic representation.
 * Contains a cache that grows as the traversers enumerate the explicit representation of the subtree.
 */
public class MddSymbolicNodeImpl implements hu.bme.mit.delta.java.mdd.MddSymbolicNode {

    private final SymbolicRepresentation symbolicRepresentation;
    private final ExplicitRepresentation explicitRepresentation;

    // MddNodeból lopva
    private final DdLevel<MddNode> level;
    private final int hashCode;
    private int references = 0;

    public MddSymbolicNodeImpl(SymbolicRepresentation symbolicRepresentation, DdLevel<MddNode> level) {
        this.symbolicRepresentation = symbolicRepresentation;
        this.level = level;
        this.hashCode = symbolicRepresentation.hashCode();

        this.explicitRepresentation = new ExplicitRepresentation();
    }

    public MddSymbolicNodeImpl(Pair<Object, MddVariable> symbolicRepresentation, DdLevel<MddNode> level) {
        this(new SymbolicRepresentation(symbolicRepresentation), level);
    }

    public MddSymbolicNodeImpl(SymbolicRepresentation symbolicRepresentation){
        this(symbolicRepresentation, symbolicRepresentation.value.second != null ? symbolicRepresentation.value.second.getLevel() : null);
    }

    public MddSymbolicNodeImpl(Pair<Object, MddVariable> symbolicRepresentation) {
        this(new SymbolicRepresentation(symbolicRepresentation), symbolicRepresentation.second != null ? symbolicRepresentation.second.getLevel() : null);
    }

    /**
     * This is a wrapper around the symbolic representation that ensures comparability of templates and nodes.
     */
    public static class SymbolicRepresentation {
        private final Pair<Object, MddVariable> value;

        private SymbolicRepresentation(final Pair<Object, MddVariable> value) {
            this.value = value;
        }

        public static SymbolicRepresentation of(final Pair<Object, MddVariable> value){
            return new SymbolicRepresentation(value);
        }

        @Override
        public boolean equals(Object that) {
            if (this == that) return true;
            if (that instanceof SymbolicRepresentation) {
                return Objects.equals(value, ((SymbolicRepresentation) that).value);
            }
            if (that instanceof MddSymbolicNodeImpl) {
                return Objects.equals(value, ((MddSymbolicNodeImpl) that).symbolicRepresentation.value);
            }
            return false;
        }

        @Override
        public int hashCode() {
            return value.hashCode();

        }
    }

    /**
     * This class handles the cache.
     */
    public static class ExplicitRepresentation {
        private final HashIntObjMap<MddNode> cache;
        private final GrowingIntArray edgeOrdering;
        private MddSymbolicNodeImpl defaultValue;
        private boolean complete;

        public ExplicitRepresentation() {
            this.cache = HashIntObjMaps.newUpdatableMap();
            this.edgeOrdering = new GrowingIntArray(100, 100);
            this.defaultValue = null;
            this.complete = false;
        }

        public void cacheNode(int key, MddNode node){
            Preconditions.checkState(!complete);
            Preconditions.checkState(defaultValue == null);
            this.cache.put(key, node);
            this.edgeOrdering.add(key);
        }

        public void cacheDefault(MddSymbolicNodeImpl defaultValue){
            Preconditions.checkState(!complete);
            this.defaultValue = defaultValue;
        }

        public void setComplete(){
            this.complete = true;
        }

        public IntObjMapView<MddNode> getCacheView(){
            return IntObjMapView.of(cache, defaultValue);
        }

        public boolean isComplete(){
            return complete;
        }

        public int getEdge(int index){
            return edgeOrdering.get(index);
        }

        public int getSize(){
            return edgeOrdering.getSize();
        }
    }

    @Override
    public Pair<Object, MddVariable> getSymbolicRepresentation() {
        return symbolicRepresentation.value;
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
    public boolean isTerminal() {
        return symbolicRepresentation.value.second == null;
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

    public ExplicitRepresentation getExplicitRepresentation() {
        return explicitRepresentation;
    }

    public IntObjMapView<MddNode> getCacheView() {
        return explicitRepresentation.getCacheView();
    }

    public boolean isComplete() {
        return explicitRepresentation.isComplete() || isTerminal();
    }
}
