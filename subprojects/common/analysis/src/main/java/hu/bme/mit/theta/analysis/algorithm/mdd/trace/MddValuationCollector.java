/*
 *  Copyright 2026 Budapest University of Technology and Economics
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
package hu.bme.mit.theta.analysis.algorithm.mdd.trace;

import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Eq;
import static hu.bme.mit.theta.core.type.booltype.SmartBoolExprs.And;
import static hu.bme.mit.theta.core.type.booltype.SmartBoolExprs.Or;

import hu.bme.mit.delta.java.mdd.MddHandle;
import hu.bme.mit.delta.java.mdd.MddVariable;
import hu.bme.mit.theta.analysis.algorithm.mdd.node.expression.LitExprConverter;
import hu.bme.mit.theta.analysis.algorithm.mdd.node.expression.MddValues;
import hu.bme.mit.theta.common.collection.CollectionUtil;
import hu.bme.mit.theta.core.decl.Decl;
import hu.bme.mit.theta.core.model.ImmutableValuation;
import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import java.util.ArrayList;
import java.util.List;
import java.util.Set;
import java.util.Stack;
import java.util.function.BiConsumer;
import java.util.function.Consumer;

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
        final Set<Valuation> valuations = CollectionUtil.createSet();
        collect(node, valuations::add);
        return valuations;
    }

    /**
     * Streams every vector of the subtree to {@code consumer} without collecting them into a set.
     */
    public static void collect(MddHandle node, Consumer<Valuation> consumer) {
        walk(
                node,
                new Stack<>(),
                (assignments, terminal) -> consumer.accept(toValuation(assignments)));
    }

    /**
     * The vectors of the subtree as an expression: the literal keys of each path and, with symbolic
     * values, the formula of its terminal.
     */
    public static Expr<BoolType> toExpr(MddHandle node) {
        final MddValues values = MddValues.of(node.getVariableHandle().getMddGraph());
        final List<Expr<BoolType>> paths = new ArrayList<>();
        walk(
                node,
                new Stack<>(),
                (assignments, terminal) -> {
                    final List<Expr<BoolType>> conjuncts = new ArrayList<>();
                    for (Assignment ass : assignments) {
                        if (values.isToken(ass.value)) continue;
                        final Decl<?> decl = ass.variable.getTraceInfo(Decl.class);
                        conjuncts.add(
                                Eq(decl.getRef(), values.toLitExpr(ass.value, decl.getType())));
                    }
                    conjuncts.add(values.formulaOf(terminal.getNode()));
                    paths.add(And(conjuncts));
                });
        return Or(paths);
    }

    private static void walk(
            MddHandle node,
            Stack<Assignment> assignments,
            BiConsumer<Stack<Assignment>, MddHandle> atTerminal) {
        if (node.isTerminal()) {
            atTerminal.accept(assignments, node);
        } else {
            if (!node.defaultValue().isTerminalZero()) {

                walk(node.defaultValue(), assignments, atTerminal);

            } else {
                for (var cursor = node.cursor(); cursor.moveNext(); ) {

                    assignments.push(
                            new Assignment(
                                    node.getVariableHandle().getVariable().orElseThrow(),
                                    cursor.key()));

                    walk((MddHandle) cursor.value(), assignments, atTerminal);

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
