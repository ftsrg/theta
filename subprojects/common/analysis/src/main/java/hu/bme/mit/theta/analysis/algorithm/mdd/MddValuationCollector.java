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

import hu.bme.mit.delta.java.mdd.MddHandle;
import hu.bme.mit.delta.java.mdd.MddVariable;
import hu.bme.mit.theta.analysis.algorithm.mdd.expressionnode.LitExprConverter;
import hu.bme.mit.theta.common.container.Containers;
import hu.bme.mit.theta.core.decl.Decl;
import hu.bme.mit.theta.core.model.ImmutableValuation;
import hu.bme.mit.theta.core.model.Valuation;
import java.util.Set;
import java.util.Stack;

/**
 * A utility class for collecting all vectors from a subtree represented by a symbolic node. Only
 * works with finite diagrams, but can handle default edges.
 */
public class MddValuationCollector {

    private static class Assignment {
        final MddVariable variable;
        final Integer value;

        private Assignment(MddVariable variable, Integer value) {
            this.variable = variable;
            this.value = value;
        }
    }

    /**
     * Collect all vectors from the subtree represented by a symbolic node.
     *
     * @param node the node
     * @return the set of vectors represented by the node
     */
    public static Set<Valuation> collect(MddHandle node) {
        final Stack<Assignment> assignments = new Stack<>();
        final Set<Valuation> valuations = Containers.createSet();

        collect(node, assignments, valuations);

        return valuations;
    }

    private static void collect(
            MddHandle node, Stack<Assignment> assignments, Set<Valuation> valuations) {
        if (node.isTerminal()) {
            valuations.add(toValuation(assignments));
        } else {
            if (!node.defaultValue().isTerminalZero()) {

                collect(node.defaultValue(), assignments, valuations);

            } else {
                for (var cursor = node.cursor(); cursor.moveNext(); ) {

                    assignments.push(
                            new Assignment(
                                    node.getVariableHandle().getVariable().orElseThrow(),
                                    cursor.key()));

                    collect((MddHandle) cursor.value(), assignments, valuations);

                    assignments.pop();
                }
            }
        }
    }

    private static Valuation toValuation(Stack<Assignment> assignments) {
        final var builder = ImmutableValuation.builder();
        assignments.forEach(
                ass -> {
                    var decl = ass.variable.getTraceInfo(Decl.class);
                    builder.put(decl, LitExprConverter.toLitExpr(ass.value, decl.getType()));
                });
        return builder.build();
    }
}
