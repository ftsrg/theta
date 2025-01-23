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
package hu.bme.mit.theta.analysis.algorithm.arg;

import static com.google.common.base.Objects.equal;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.State;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

/**
 * Structural comparisons using equal() and hashCode() for ARG-related classes. Each node is
 * uniquely identifiable using its incoming edge (or its absence), and wrapped state. Each edge is
 * uniquely identifiable using its source node, and wrapped action. An ARG is uniquely identifiable
 * using its leaf nodes. An ArgTrace is uniquely identifiable using its last node.
 *
 * <p>We perform caching for the hash codes, but equals() checks will always traverse the ancestors
 * of a node (and edge). However, this traversal only goes towards the root, rather than in all
 * directions.
 */
public final class ArgStructuralEquality {
    private static final Map<Object, Integer> hashCodeCache = new LinkedHashMap<>();

    private ArgStructuralEquality() {}

    public static boolean equals(
            final ArgNode<? extends State, ? extends Action> n1,
            final ArgNode<? extends State, ? extends Action> n2) {

        // if references are the same, the two nodes are equal
        if (n1 == n2) {
            return true;
        }

        // if one is null, the two nodes are not equal
        if (n1 == null || n2 == null) {
            return false;
        }

        // if wrapped state is not same, nodes are not equal
        if (!n1.getState().equals(n2.getState())) {
            return false;
        }

        // if one node has a parent but the other one does not, nodes are not equal
        if (n1.inEdge.isPresent() != n2.inEdge.isPresent()) {
            return false;
        }

        // if in edge is not same, nodes are not equal
        if (n1.inEdge.isPresent() && !equals(n1.inEdge.get(), n2.inEdge.get())) {
            return false;
        }

        return true;
    }

    public static boolean equals(
            final ArgEdge<? extends State, ? extends Action> e1,
            final ArgEdge<? extends State, ? extends Action> e2) {

        // if references are the same, the two edges are equal
        if (e1 == e2) {
            return true;
        }

        // if one is null, the two edges are not equal
        if (e1 == null || e2 == null) {
            return false;
        }

        // if wrapped action is not same, edges are not equal
        if (!e1.getAction().equals(e2.getAction())) {
            return false;
        }

        // if source node is not same, edges are not equal
        if (!equals(e1.getSource(), e2.getSource())) {
            return false;
        }

        return true;
    }

    public static boolean equals(
            final ARG<? extends State, ? extends Action> a1,
            final ARG<? extends State, ? extends Action> a2) {

        // if references are the same, the two edges are equal
        if (a1 == a2) {
            return true;
        }

        // if one is null, the two args are not equal
        if (a1 == null || a2 == null) {
            return false;
        }

        Set<ArgNode<? extends State, ? extends Action>> leaves1 =
                a1.getNodes().filter(ArgNode::isLeaf).collect(Collectors.toUnmodifiableSet());
        Set<ArgNode<? extends State, ? extends Action>> leaves2 =
                a2.getNodes().filter(ArgNode::isLeaf).collect(Collectors.toUnmodifiableSet());

        // if the two ARGs contain a different number of leaf nodes, they are not equal
        if (leaves1.size() != leaves2.size()) {
            return false;
        }

        leaves1loop:
        for (ArgNode<? extends State, ? extends Action> n1 : leaves1) {
            for (ArgNode<? extends State, ? extends Action> n2 : leaves2) {
                if (equals(n1, n2)) {
                    continue leaves1loop;
                }
            }
            // a leaf node did not have a corresponding leaf node in the other arg
            return false;
        }
        return true;
    }

    public static boolean equals(
            final ArgTrace<? extends State, ? extends Action> t1,
            final ArgTrace<? extends State, ? extends Action> t2) {

        return equal(t1.node(t1.length()), t2.node(t2.length()));
    }

    public static int hashCode(final ArgNode<? extends State, ? extends Action> n) {
        if (!hashCodeCache.containsKey(n)) {
            int hashcode = 0;

            if (n.inEdge.isPresent()) {
                hashcode += hashCode(n.inEdge.get());
            }

            hashcode += n.getState().hashCode();
            hashCodeCache.put(n, hashcode);
        }
        return hashCodeCache.get(n);
    }

    public static int hashCode(final ArgEdge<? extends State, ? extends Action> e) {
        if (!hashCodeCache.containsKey(e)) {
            int hashcode = 0;

            hashcode += hashCode(e.getSource());

            hashcode += e.getAction().hashCode();

            hashCodeCache.put(e, hashcode);
        }
        return hashCodeCache.get(e);
    }

    // ARG is not immutable, so we don't cache
    public static int hashCode(final ARG<? extends State, ? extends Action> a) {
        int hashcode = 0;

        Set<ArgNode<? extends State, ? extends Action>> leaves =
                a.getNodes().filter(ArgNode::isLeaf).collect(Collectors.toUnmodifiableSet());
        for (ArgNode<? extends State, ? extends Action> leaf : leaves) {
            hashcode += hashCode(leaf);
        }

        return hashcode;
    }

    public static int hashCode(final ArgTrace<? extends State, ? extends Action> t) {
        if (!hashCodeCache.containsKey(t)) {
            int hashcode = hashCode(t.node(t.length()));
            hashCodeCache.put(t, hashcode);
        }
        return hashCodeCache.get(t);
    }
}
