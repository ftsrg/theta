package hu.bme.mit.theta.analysis.algorithm.symbolic.symbolicnode.expression;

import hu.bme.mit.delta.Pair;
import hu.bme.mit.delta.java.mdd.MddVariable;
import hu.bme.mit.theta.analysis.algorithm.symbolic.symbolicnode.MddSymbolicNode;
import hu.bme.mit.theta.analysis.algorithm.symbolic.symbolicnode.MddSymbolicNodeTraverser;
import hu.bme.mit.theta.analysis.algorithm.symbolic.symbolicnode.TraversalConstraint;
import hu.bme.mit.theta.core.decl.ConstDecl;
import hu.bme.mit.theta.solver.Solver;

import java.util.Optional;
import java.util.function.Supplier;

import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Geq;
import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Leq;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;

public class ConstrainedExprNodeTraverser implements MddSymbolicNodeTraverser {

    final ExprNodeTraverser wrapped;

    public ConstrainedExprNodeTraverser(MddSymbolicNode rootNode, Supplier<Solver> solverSupplier, TraversalConstraint constraint) {
        final Solver solver = solverSupplier.get();
        solver.push();

        Optional<? extends MddVariable> nextVariable = Optional.of(rootNode.getSymbolicRepresentation().second);
        while (nextVariable.isPresent()){
            final MddVariable variable = nextVariable.get();
            final Optional<Pair<Integer, Integer>> bounds = constraint.getBoundsFor(variable);
            if(bounds.isPresent()){
                solver.add(Geq(variable.getTraceInfo(ConstDecl.class).getRef(), Int(bounds.get().first)));
                solver.add(Leq(variable.getTraceInfo(ConstDecl.class).getRef(), Int(bounds.get().second)));
            }
            nextVariable = variable.getLower();
        }

        wrapped = new ExprNodeTraverser(rootNode, () -> solver);
    }

    @Override
    public MddSymbolicNode getCurrentNode() {
        return wrapped.getCurrentNode();
    }

    @Override
    public MddSymbolicNode moveUp() {
        return wrapped.moveUp();
    }

    @Override
    public MddSymbolicNode moveDown(int assignment) {
        return wrapped.moveDown(assignment);
    }

    @Override
    public QueryResult queryEdge() {
        return wrapped.queryEdge();
    }

    @Override
    public boolean queryEdge(int assignment) {
        return wrapped.queryEdge(assignment);
    }

    @Override
    public MddSymbolicNode peakDown(int assignment) {
        return wrapped.peakDown(assignment);
    }
}
