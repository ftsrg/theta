package hu.bme.mit.theta.analysis.algorithm.symbolic.symbolicnode;

import com.google.common.base.Preconditions;
import hu.bme.mit.delta.java.mdd.MddVariable;
import hu.bme.mit.theta.analysis.algorithm.symbolic.symbolicnode.expression.LitExprConverter;
import hu.bme.mit.theta.common.container.Containers;
import hu.bme.mit.theta.core.decl.ConstDecl;
import hu.bme.mit.theta.core.model.ImmutableValuation;
import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.LitExpr;

import java.util.Set;
import java.util.Stack;

/**
 * A utility class for collecting all vectors from a subtree represented by a symbolic node.
 * Only works with finite diagrams, but can handle default edges.
 */
public class ValuationCollector {

    private static class Assignment{
        final ConstDecl<?> decl;
        final LitExpr<?> value;

        private Assignment(ConstDecl<?> decl, LitExpr<?> value) {
            this.decl = decl;
            this.value = value;
        }
    }

    /**
     * Collect all vectors from the subtree represented by a symbolic node.
     * @param node the symbolic node
     * @param traverser the traverser that will be used to enumerate the subtree. Must start on the node.
     * @return the set of vectors represented by the node
     */
    public static Set<Valuation> collect(MddSymbolicNodeImpl node, MddSymbolicNodeTraverser traverser){
        Preconditions.checkState(traverser.getCurrentNode().equals(node));

        final Stack<Assignment> assignments = new Stack<>();
        final Set<Valuation> valuations = Containers.createSet();

        collect(node, traverser, assignments, valuations);

        return valuations;
    }

    public static void collect(MddSymbolicNodeImpl node, MddSymbolicNodeTraverser traverser, Stack<Assignment> assignments, Set<Valuation> valuations){
        final MddVariable variable = node.getSymbolicRepresentation().second;

        if(node.isTerminal()){
            valuations.add(toValuation(assignments));
        } else {
            if(node.getCacheView().defaultValue() != null){
                traverser.moveDown(0); // move down along arbitrary edge

                collect((MddSymbolicNodeImpl) node.getCacheView().defaultValue(), traverser, assignments, valuations);

                traverser.moveUp();
            } else {
                while (!node.isComplete()) traverser.queryEdge();
                for (var cur = node.getCacheView().cursor(); cur.moveNext(); ) {
                    assert cur.value() != null;

                    assignments.push(new Assignment(variable.getTraceInfo(ConstDecl.class), LitExprConverter.toLitExpr(cur.key(), variable.getTraceInfo(ConstDecl.class).getType())));
                    traverser.moveDown(cur.key());

                    collect((MddSymbolicNodeImpl) cur.value(), traverser, assignments, valuations);

                    assignments.pop();
                    traverser.moveUp();
                }
            }
        }
    }

    private static Valuation toValuation(Stack<Assignment> assignments){
        final var builder = ImmutableValuation.builder();
        assignments.stream().forEach(ass -> builder.put(ass.decl, ass.value));
        return builder.build();
    }


}
