package hu.bme.mit.theta.analysis.algorithm.symbolic.expression;

import com.google.common.base.Preconditions;
import hu.bme.mit.delta.Pair;
import hu.bme.mit.delta.collections.IntObjCursor;
import hu.bme.mit.delta.java.DdLevel;
import hu.bme.mit.delta.java.mdd.MddNode;
import hu.bme.mit.delta.java.mdd.MddSymbolicNode;
import hu.bme.mit.delta.java.mdd.MddVariable;
import hu.bme.mit.theta.core.decl.Decl;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.solver.SolverFactory;

public class ExpressionNode implements MddSymbolicNode {

    private final Pair<Expr<BoolType>, MddVariable> decision;

    // MddNodeból lopva
    private final DdLevel<MddNode> level;
    private final int              hashCode;
    private       int              references = 0;

    private final AssignmentEnumerator enumerator;

    public ExpressionNode(Pair<Expr<BoolType>, MddVariable> decision, DdLevel<MddNode> level, int hashCode, SolverFactory solverFactory) {
        this.decision = decision;
        this.level = level;
        this.hashCode = hashCode;

        this.enumerator = new AssignmentEnumerator<>(decision.first, decision.second.getTraceInfo(Decl.class), solverFactory.createSolver());
    }

    @Override
    public MddVariable getVariable() {
        return decision.second;
    }

    @Override
    public Object getSymbolicRepresentation() {
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
        for (IntObjCursor<? extends MddNode> c = this.cursor(); c.moveNext(); ) {
            c.value().acquire();
        }
        if ((this.defaultValue() != null) && (this.defaultValue() != this)) {
            this.defaultValue().acquire();
        }
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
        for (IntObjCursor<? extends MddNode> c = this.cursor(); c.moveNext(); ) {
            c.value().release();
        }
        if ((this.defaultValue() != null) && (this.defaultValue() != this)) {
            this.defaultValue().release();
        }
    }

    @Override
    public int getReferenceCount() {
        return references;
    }

    @Override
    public boolean isEmpty() {
        return !enumerator.isSat();
    }

    @Override
    public boolean isProcedural() {
        return false;
    }

    @Override
    public boolean containsKey(int key) {
        // Check if sat -> true
        // Cache model if found
        return enumerator.isValidAssignment(LitExprConverter.toLitExpr(key, decision.second.getTraceInfo(Decl.class).getType()));
    }

    @Override
    public MddNode get(int key) {
        if (enumerator.isValidAssignment(LitExprConverter.toLitExpr(key, decision.second.getTraceInfo(Decl.class).getType()))){
            // Simplify expr, ask for new node with simplified expr, cache child
        }
        return null;
    }

    @Override
    public MddNode defaultValue() {
        // Kéne a terminal 0-ra egy referencia
        return null;
    }

    @Override
    public IntObjCursor<? extends MddNode> cursor() {
        // Kéne egy custom cursor ami lazyn felsorolja az összes értéket amivel sat
        // Amit tud, azt először vegye ki a children cacheből: nem elég egyszer, hanem mindig meg kell nézni, hogy nincs-e új ami azóta cachelődött
//        return new LazyCursor<ExpressionNode>(this, initializer, cacher);
        return new LazyCursor<>(enumerator);
    }

    @Override
    public int size() {
        // Na ez drága lesz
        return 0;
    }
}
