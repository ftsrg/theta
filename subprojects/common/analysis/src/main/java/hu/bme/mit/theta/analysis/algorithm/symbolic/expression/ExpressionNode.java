package hu.bme.mit.theta.analysis.algorithm.symbolic.expression;

import com.google.common.base.Preconditions;
import com.koloboke.collect.map.IntObjMap;
import com.koloboke.collect.map.hash.HashIntObjMap;
import com.koloboke.collect.map.hash.HashIntObjMaps;
import hu.bme.mit.delta.Pair;
import hu.bme.mit.delta.collections.IntObjMapView;
import hu.bme.mit.delta.collections.impl.IntObjMapViews;
import hu.bme.mit.delta.java.DdLevel;
import hu.bme.mit.delta.java.mdd.MddNode;
import hu.bme.mit.delta.java.mdd.MddVariable;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;

public class ExpressionNode implements IMddSymbolicNode{

    private final Pair<Expr<BoolType>, MddVariable> decision;

    // MddNodeból lopva
    private final DdLevel<MddNode> level;
    private final int              hashCode;
    private       int              references = 0;

    private final HashIntObjMap<ExpressionNode> cache;

    private ExpressionNode defaultValue;

    private boolean complete;

    public ExpressionNode(Pair<Expr<BoolType>, MddVariable> decision, DdLevel<MddNode> level, int hashCode) {
        this.decision = decision;
        this.level = level;
        this.hashCode = hashCode;

        this.cache = HashIntObjMaps.newMutableMap();
        this.defaultValue = null;
        this.complete = false;
    }

    @Override
    public MddVariable getVariable() {
        return decision.second;
    }

    @Override
    public Object getSymbolicRepresentation() {
        return decision;
    }

    public Pair<Expr<BoolType>, MddVariable> getDecision(){
        return decision;
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

    public void cacheNode(int key, ExpressionNode node){
        if(!complete) this.cache.put(key, node);
    }

    public void cacheDefault(ExpressionNode defaultValue){
        Preconditions.checkArgument(!complete);
        this.defaultValue = defaultValue;
    }

    public void setComplete(){
        this.complete = true;
    }

    public IntObjMapView<ExpressionNode> getCacheView(){
        return IntObjMapView.of(cache, defaultValue);
    }

    public boolean isComplete(){
        return complete;
    }
}
