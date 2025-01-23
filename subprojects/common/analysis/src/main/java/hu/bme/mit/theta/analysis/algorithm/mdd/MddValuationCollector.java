/*
 *  Copyright 2025 Budapest University of Technology and Economics
 *
 *  Licensed under the Apache License, Version 2.0 (the "License");
 *  you may not use this file except in compliance with the License.
 *  You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 *  Unless required by applicable law or agreed to in writing, software
 *  distributed under the License is distributed on an "AS IS" BASIS,
 *  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *  See the License for the specific language governing permissions and
 *  limitations under the License.
 */
package hu.bme.mit.theta.analysis.algorithm.mdd;

import hu.bme.mit.delta.collections.RecursiveIntObjCursor;
import hu.bme.mit.delta.java.mdd.MddNode;
import hu.bme.mit.theta.analysis.algorithm.mdd.expressionnode.LitExprConverter;
import hu.bme.mit.theta.analysis.algorithm.mdd.expressionnode.MddExpressionRepresentation;
import hu.bme.mit.theta.common.container.Containers;
import hu.bme.mit.theta.core.decl.Decl;
import hu.bme.mit.theta.core.model.ImmutableValuation;
import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.LitExpr;
import java.util.Set;
import java.util.Stack;

/**
 * A utility class for collecting all vectors from a subtree represented by a symbolic node. Only
 * works with finite diagrams, but can handle default edges.
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
     * @param node the node
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

    private static void collect(
            MddNode node,
            RecursiveIntObjCursor<? extends MddNode> cursor,
            Stack<Assignment> assignments,
            Set<Valuation> valuations) {
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
                        final MddExpressionRepresentation representation =
                                (MddExpressionRepresentation) node.getRepresentation();
                        assignments.push(
                                new Assignment(
                                        representation.getDecl(),
                                        LitExprConverter.toLitExpr(
                                                cursor.key(), representation.getDecl().getType())));
                    }

                    try (var valueCursor = cursor.valueCursor()) {
                        collect(cursor.value(), valueCursor, assignments, valuations);
                    }

                    if (node.getRepresentation() instanceof MddExpressionRepresentation)
                        assignments.pop();
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
