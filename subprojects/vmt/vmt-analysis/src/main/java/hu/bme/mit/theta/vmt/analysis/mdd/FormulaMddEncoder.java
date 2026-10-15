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
package hu.bme.mit.theta.vmt.analysis.mdd;

import hu.bme.mit.delta.java.mdd.BinaryOperationCache;
import hu.bme.mit.delta.java.mdd.MddHandle;
import hu.bme.mit.delta.java.mdd.MddNode;
import hu.bme.mit.delta.java.mdd.MddVariable;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Deque;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.BooleanFormulaManager;
import org.sosy_lab.java_smt.api.FormulaType;

/**
 * Exact encodings of an MDD as a formula, the JavaSMT counterparts of {@code MddToExprNodeLevel}
 * and {@code MddToExprVectorLevel}. The node-level encoding names every node with a fresh boolean
 * variable defined by the disjunction of its edges, so shared nodes are encoded once; the
 * vector-level encoding is the disjunction of all paths.
 *
 * <p>One encoder belongs to one {@link FormulaMddContext}: the fresh variables and the caches are
 * only valid for its formula manager.
 */
public final class FormulaMddEncoder {

    private static final String NODE_VAR_PREFIX = "__mdd_node_";

    private final FormulaMddContext ctx;
    private final BooleanFormulaManager bmgr;
    private final BinaryOperationCache<MddNode, MddVariable, BooleanFormula> representatives =
            new BinaryOperationCache<>();
    private final BinaryOperationCache<MddNode, MddVariable, BooleanFormula> definitions =
            new BinaryOperationCache<>();
    private final BinaryOperationCache<MddNode, MddVariable, BooleanFormula> encodings =
            new BinaryOperationCache<>();
    private int nodeVarCount = 0;

    FormulaMddEncoder(FormulaMddContext ctx) {
        this.ctx = ctx;
        this.bmgr = ctx.getBooleanFormulaManager();
    }

    public BooleanFormula nodeLevel(MddHandle root) {
        return nodeLevel(root.getNode(), root.getVariableHandle().getVariable().orElseThrow());
    }

    public BooleanFormula nodeLevel(MddNode root, MddVariable variable) {
        final BooleanFormula cached = encodings.getOrNull(root, variable);
        if (cached != null) return cached;

        final Set<NodeAtLevel> visited = new HashSet<>();
        final Deque<NodeAtLevel> stack = new ArrayDeque<>();
        stack.push(new NodeAtLevel(root, variable));
        final List<BooleanFormula> constraints = new ArrayList<>();
        while (!stack.isEmpty()) {
            final NodeAtLevel current = stack.pop();
            if (!visited.add(current)) continue;
            constraints.add(definition(current.node(), current.variable()));
            if (!current.node().isTerminal() && current.variable().getLower().isPresent()) {
                final MddVariable lower = current.variable().getLower().get();
                final MddNode defaultNode = current.node().defaultValue();
                if (defaultNode != null) {
                    stack.push(new NodeAtLevel(defaultNode, lower));
                } else {
                    for (var cursor = current.node().cursor(); cursor.moveNext(); ) {
                        stack.push(new NodeAtLevel(cursor.value(), lower));
                    }
                }
            }
        }
        constraints.add(representative(root, variable));
        final BooleanFormula result = bmgr.and(constraints);
        encodings.addToCache(root, variable, result);
        return result;
    }

    private record NodeAtLevel(MddNode node, MddVariable variable) {}

    private BooleanFormula representative(MddNode node, MddVariable variable) {
        if (node.isTerminal()) return bmgr.makeTrue();
        final BooleanFormula cached = representatives.getOrNull(node, variable);
        if (cached != null) return cached;
        final BooleanFormula fresh =
                ctx.getFormulaManager()
                        .makeVariable(FormulaType.BooleanType, NODE_VAR_PREFIX + nodeVarCount++);
        representatives.addToCache(node, variable, fresh);
        return fresh;
    }

    private BooleanFormula definition(MddNode node, MddVariable variable) {
        final BooleanFormula cached = definitions.getOrNull(node, variable);
        if (cached != null) return cached;
        final BooleanFormula representative = representative(node, variable);
        final BooleanFormula definition;
        if (node.isTerminal()) {
            definition = representative;
        } else if (node.defaultValue() == null) {
            final FormulaVar var = (FormulaVar) variable.getTraceInfo();
            final MddVariable lower = variable.getLower().orElse(null);
            final List<BooleanFormula> disjuncts = new ArrayList<>();
            for (var cursor = node.cursor(); cursor.moveNext(); ) {
                disjuncts.add(
                        bmgr.and(
                                ctx.equal(var, ctx.toValueFormula(cursor.key(), var)),
                                representative(cursor.value(), lower)));
            }
            definition = bmgr.equivalence(representative, bmgr.or(disjuncts));
        } else {
            definition =
                    bmgr.equivalence(
                            representative,
                            representative(node.defaultValue(), variable.getLower().orElse(null)));
        }
        definitions.addToCache(node, variable, definition);
        return definition;
    }

    /** The disjunction of all paths; only usable for small MDDs. */
    public BooleanFormula vectorLevel(MddHandle root) {
        final List<BooleanFormula> paths = new ArrayList<>();
        collectPaths(root, new ArrayList<>(), paths);
        return bmgr.or(paths);
    }

    private void collectPaths(
            MddHandle node, List<BooleanFormula> assignments, List<BooleanFormula> paths) {
        if (node.isTerminal()) {
            if (!node.isTerminalZero()) paths.add(bmgr.and(assignments));
            return;
        }
        if (!node.defaultValue().isTerminalZero()) {
            collectPaths(node.defaultValue(), assignments, paths);
            return;
        }
        final FormulaVar var =
                (FormulaVar) node.getVariableHandle().getVariable().orElseThrow().getTraceInfo();
        for (var cursor = node.cursor(); cursor.moveNext(); ) {
            assignments.add(ctx.equal(var, ctx.toValueFormula(cursor.key(), var)));
            collectPaths((MddHandle) cursor.value(), assignments, paths);
            assignments.remove(assignments.size() - 1);
        }
    }
}
