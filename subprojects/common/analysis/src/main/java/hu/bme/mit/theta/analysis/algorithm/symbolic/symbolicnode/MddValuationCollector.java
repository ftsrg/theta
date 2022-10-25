package hu.bme.mit.theta.analysis.algorithm.symbolic.symbolicnode;

import hu.bme.mit.delta.collections.RecursiveIntObjCursor;
import hu.bme.mit.delta.java.mdd.MddNode;
import hu.bme.mit.theta.analysis.algorithm.symbolic.symbolicnode.expression.LitExprConverter;
import hu.bme.mit.theta.analysis.algorithm.symbolic.symbolicnode.expression.MddExpressionRepresentation;
import hu.bme.mit.theta.common.container.Containers;
import hu.bme.mit.theta.core.decl.Decl;
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

    private static class Assignment {
        final Decl<?> decl;
        final LitExpr<?> value;

        private Assignment(Decl<?> decl, LitExpr<?> value) {
            this.decl = decl;
            this.value = value;
        }
    }

    /**
     * Collect all vectors from the subtree represented by a symbolic node.
     *
     * @param interpretation intrerpretation of the node
     * @return the set of vectors represented by the node
     */
    public static Set<Valuation> collect(MddNode node) {
        final Stack<Assignment> assignments = new Stack<>();
        final Set<Valuation> valuations = Containers.createSet();

        try (var cursor = node.cursor()) {
            collect(node, cursor, assignments, valuations);
        }

        return valuations;
    }

    public static void collect(MddNode node, RecursiveIntObjCursor<? extends MddNode> cursor, Stack<Assignment> assignments, Set<Valuation> valuations) {
        if (node.isTerminal()) {
            valuations.add(toValuation(assignments));
        } else {
            if (node.defaultValue() != null) {
                cursor.moveNext();

                try (var valueCursor = cursor.valueCursor()) {
                    collect(node.defaultValue(), valueCursor, assignments, valuations);
                }

            } else {
                while (cursor.moveNext()) {
                    assert cursor.value() != null;

                    if (node.getRepresentation() instanceof MddExpressionRepresentation) {
                        final MddExpressionRepresentation representation = (MddExpressionRepresentation) node.getRepresentation();
                        assignments.push(new Assignment(representation.getDecl(), LitExprConverter.toLitExpr(cursor.key(), representation.getDecl().getType())));
                    }

                    try (var valueCursor = cursor.valueCursor()) {
                        collect(cursor.value(), valueCursor, assignments, valuations);
                    }

                    if (node.getRepresentation() instanceof MddExpressionRepresentation) assignments.pop();

                }
            }
        }
    }

    private static Valuation toValuation(Stack<Assignment> assignments) {
        final var builder = ImmutableValuation.builder();
        assignments.stream().forEach(ass -> builder.put(ass.decl, ass.value));
        return builder.build();
    }


}
