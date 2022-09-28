package hu.bme.mit.theta.analysis.algorithm.symbolic.symbolicnode;

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
public class MddValuationCollector {

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
     * @param interpretation intrerpretation of the node
     * @return the set of vectors represented by the node
     */
    public static Set<Valuation> collect(MddSymbolicNodeInterpretation interpretation){
        final Stack<Assignment> assignments = new Stack<>();
        final Set<Valuation> valuations = Containers.createSet();

        try(var cursor = interpretation.cursor()){
            collect(interpretation.getNode(), cursor, assignments, valuations);
        }

        return valuations;
    }

    public static void collect(MddSymbolicNode node, RecursiveCursor<? extends MddSymbolicNode> cursor, Stack<Assignment> assignments, Set<Valuation> valuations){
        final MddVariable variable = node.getSymbolicRepresentation().second;

        if(node.isTerminal()){
            valuations.add(toValuation(assignments));
        } else {
            if(node.getCacheView().defaultValue() != null){
                cursor.moveNext();

                try(var valueCursor = cursor.valueCursor()){
                    collect(node.getCacheView().defaultValue(), valueCursor, assignments, valuations);
                }

            } else {
                while (cursor.moveNext()) {
                    assert cursor.value() != null;

                    assignments.push(new Assignment(variable.getTraceInfo(ConstDecl.class), LitExprConverter.toLitExpr(cursor.key(), variable.getTraceInfo(ConstDecl.class).getType())));

                    try(var valueCursor = cursor.valueCursor()){
                        collect(cursor.value(), valueCursor, assignments, valuations);
                    }

                    assignments.pop();

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
