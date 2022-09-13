package hu.bme.mit.theta.analysis.algorithm.symbolic.symbolicnode.expression;

import hu.bme.mit.delta.Pair;
import hu.bme.mit.delta.java.mdd.MddVariable;
import hu.bme.mit.theta.analysis.algorithm.symbolic.symbolicnode.MddSymbolicNodeImpl;
import hu.bme.mit.theta.analysis.algorithm.symbolic.symbolicnode.MddSymbolicNodeTraverser;
import hu.bme.mit.theta.analysis.algorithm.symbolic.symbolicnode.TraversalConstraint;
import hu.bme.mit.theta.core.decl.ConstDecl;
import hu.bme.mit.theta.solver.Solver;

import java.util.Optional;
import java.util.function.Supplier;

import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Geq;
import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Leq;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;

/**
 * A constrained traverser that implements constrained traversal by "poisoning" the solver of a wrapped {@link ExprNodeTraverser} with the constraints.
 */
public class ConstrainedExprNodeTraverser implements MddSymbolicNodeTraverser {

    final ExprNodeTraverser wrapped;

    public ConstrainedExprNodeTraverser(MddSymbolicNodeImpl rootNode, Supplier<Solver> solverSupplier, TraversalConstraint constraint) {
        this.wrapped = new ExprNodeTraverser(rootNode, () -> prepareSolver(rootNode, solverSupplier, constraint));
    }

    private Solver prepareSolver(MddSymbolicNodeImpl rootNode, Supplier<Solver> solverSupplier, TraversalConstraint constraint){
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

        return solver;
    }

    @Override
    public MddSymbolicNodeImpl getCurrentNode() {
        return wrapped.getCurrentNode();
    }

    @Override
    public MddSymbolicNodeImpl moveUp() {
        return wrapped.moveUp();
    }

    @Override
    public MddSymbolicNodeImpl moveDown(int assignment) {
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
    public MddSymbolicNodeImpl peakDown(int assignment) {
        return wrapped.peakDown(assignment);
    }
}
