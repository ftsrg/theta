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
package hu.bme.mit.theta.analysis.algorithm.mdd.fixedpoint;

import hu.bme.mit.delta.java.mdd.BinaryOperationCache;
import hu.bme.mit.delta.java.mdd.MddGraph;
import hu.bme.mit.delta.java.mdd.MddNode;
import hu.bme.mit.theta.analysis.algorithm.mdd.ansd.AbstractNextStateDescriptor;
import hu.bme.mit.theta.analysis.algorithm.mdd.node.expression.MddValues;
import java.util.ArrayList;
import java.util.List;

/**
 * Saturation of a terminal: where steps act on terminals, a step can change a terminal and no key,
 * so a terminal is saturated to the least fixed point of the terminal steps of a descriptor.
 */
final class TerminalSaturation {

    private final MddGraph<?> graph;
    private final BinaryOperationCache<MddNode, AbstractNextStateDescriptor, MddNode> cache =
            new BinaryOperationCache<>();

    TerminalSaturation(MddGraph<?> graph) {
        this.graph = graph;
    }

    MddNode saturate(MddNode n, AbstractNextStateDescriptor d) {
        if (!MddValues.of(graph).actsOnTerminals()
                || n == graph.getTerminalZeroNode()
                || d == AbstractNextStateDescriptor.terminalIdentity()
                || d == AbstractNextStateDescriptor.terminalEmpty()) return n;
        MddNode ret = cache.getOrNull(n, d);
        if (ret != null) {
            return ret;
        }
        final List<AbstractNextStateDescriptor> steps = new ArrayList<>();
        collectSteps(d, steps);
        MddNode nsat = n;
        boolean changed;
        do {
            changed = false;
            for (AbstractNextStateDescriptor step : steps) {
                if (!step.evaluate()) continue;
                final MddNode nfire =
                        graph.unionTerminal(nsat, step.transformTerminal(nsat, graph));
                if (nfire != nsat) {
                    nsat = nfire;
                    changed = true;
                }
            }
        } while (changed);
        cache.addToCache(n, d, nsat);
        return nsat;
    }

    private static void collectSteps(
            AbstractNextStateDescriptor d, List<AbstractNextStateDescriptor> steps) {
        if (d == AbstractNextStateDescriptor.terminalIdentity()
                || d == AbstractNextStateDescriptor.terminalEmpty()) return;
        final var split = d.split();
        if (split.isPresent()) {
            for (AbstractNextStateDescriptor part : split.get()) {
                if (part == d) steps.add(d);
                else collectSteps(part, steps);
            }
        } else steps.add(d);
    }

    void clear() {
        cache.clear();
    }

    void cleanup() {
        cache.clearSelectively(
                (source, d, result) ->
                        source.getReferenceCount() == 0 || result.getReferenceCount() == 0);
    }
}
