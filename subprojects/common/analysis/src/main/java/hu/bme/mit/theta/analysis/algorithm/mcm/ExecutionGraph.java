/*
 *  Copyright 2022 Budapest University of Technology and Economics
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

package hu.bme.mit.theta.analysis.algorithm.mcm;

import com.google.common.collect.ImmutableList;
import hu.bme.mit.theta.common.Tuple2;
import hu.bme.mit.theta.common.Tuple3;

import java.util.ArrayList;
import java.util.Collection;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;

/**
 * Represents an execution graph (i.e., events and relations among them)
 * @param <S>   Key type for scopes
 * @param <K>   Key type for processes
 */
public class ExecutionGraph<S, K> {
    private final Map<S, Collection<K>> processesByScope;
    private final Map<K, Collection<Node<S, K>>> eventsByProcess;
    private final Map<String, Collection<Node<S, K>>> eventsByType;
    private final Map<String, Collection<Node<S, K>>> eventsByTag;
    private final Map<String, Collection<Tuple3<Node<S, K>, Node<S, K>, String>>> edges;

    public ExecutionGraph() {
        eventsByProcess = new LinkedHashMap<>();
        eventsByType = new LinkedHashMap<>();
        edges = new LinkedHashMap<>();
        processesByScope = new LinkedHashMap<>();
        eventsByTag = new LinkedHashMap<>();
    }

    public Node<S, K> addNode(final String name, final Tuple2<S, K> owner, final String type, final String tag) {
        processesByScope.putIfAbsent(owner.get1(), new LinkedHashSet<>());
        processesByScope.get(owner.get1()).add(owner.get2());
        final Node<S, K> newNode = new Node(name, owner, type, tag);
        eventsByType.putIfAbsent(type, new LinkedHashSet<>());
        eventsByType.get(type).add(newNode);
        eventsByTag.putIfAbsent(tag, new LinkedHashSet<>());
        eventsByTag.get(tag).add(newNode);
        eventsByProcess.putIfAbsent(owner.get2(), new LinkedHashSet<>());
        eventsByProcess.get(owner.get2()).add(newNode);
        return newNode;
    }

    public void addEdge(final Node<S, K> from, final Node<S, K> to, final String label) {
        to.incomingEdges.add(Tuple2.of(label, from));
        from.outgoingEdges.add(Tuple2.of(label, to));
    }

    public Map<String, Collection<Tuple3<Node<S, K>, Node<S, K>, String>>> getEdges() {
        return edges;
    }


    public static class Node<S, K> {
        private final String name;
        private final Tuple2<S, K> owner;
        private final String type;
        private final String tag;
        private final List<Tuple2<String, Node<S, K>>> outgoingEdges;
        private final List<Tuple2<String, Node<S, K>>> incomingEdges;

        public Node(final String name, final Tuple2<S, K> owner, final String type, final String tag) {
            this.name = name;
            this.owner = owner;
            this.type = type;
            this.tag = tag;
            outgoingEdges = new ArrayList<>();
            incomingEdges = new ArrayList<>();
        }

        public String getName() {
            return name;
        }

        public Tuple2<S, K> getOwner() {
            return owner;
        }

        public String getTag() {
            return tag;
        }

        public String getType() {
            return type;
        }

        public List<Tuple2<String, Node<S, K>>> getOutgoingEdges() {
            return ImmutableList.copyOf(outgoingEdges);
        }

        public List<Tuple2<String, Node<S, K>>> getIncomingEdges() {
            return ImmutableList.copyOf(incomingEdges);
        }
    }
}
