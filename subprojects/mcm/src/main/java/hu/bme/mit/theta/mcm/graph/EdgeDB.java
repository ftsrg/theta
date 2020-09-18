package hu.bme.mit.theta.mcm.graph;

import hu.bme.mit.theta.common.Tuple2;
import hu.bme.mit.theta.mcm.graph.classification.Thread;
import hu.bme.mit.theta.mcm.graph.classification.Variable;
import hu.bme.mit.theta.mcm.graph.classification.nodes.Fence;
import hu.bme.mit.theta.mcm.graph.classification.nodes.Node;
import hu.bme.mit.theta.mcm.graph.classification.nodes.Read;
import hu.bme.mit.theta.mcm.graph.classification.nodes.Write;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;
import java.util.function.Consumer;

import static com.google.common.base.Preconditions.checkState;

public class EdgeDB {
    private final ReflexiveLabelledMap<Node, Node, String> edges;
    private final Map<Thread, Set<Node>> threadNodeMapping;
    private final Map<Variable, Set<Node>> varNodeMapping;
    private Node lastNode;
    private final boolean onlyNodesAreValid;
    private final boolean onlyLogicalValue;
    private final boolean truth;

    public EdgeDB() {
        edges = new ReflexiveLabelledMap<>();
        onlyNodesAreValid = false;
        threadNodeMapping = new HashMap<>();
        varNodeMapping = new HashMap<>();
        lastNode = null;
        onlyLogicalValue = false;
        truth = false;
    }

    private EdgeDB(
            ReflexiveLabelledMap<Node, Node, String> newEdges,
            Map<Thread, Set<Node>> threadNodeMapping,
            Map<Variable, Set<Node>> varNodeMapping,
            Node lastNode, boolean onlyNodesAreValid) {
        this.threadNodeMapping = threadNodeMapping;
        this.varNodeMapping = varNodeMapping;
        edges = newEdges;
        this.lastNode = lastNode;
        this.onlyNodesAreValid = onlyNodesAreValid;
        onlyLogicalValue = false;
        truth = false;
    }

    private EdgeDB(boolean truth) {
        edges = null;
        threadNodeMapping = null;
        varNodeMapping = null;
        onlyNodesAreValid = false;
        onlyLogicalValue = true;
        this.truth = truth;
    }

    public static EdgeDB empty() {
        return new EdgeDB();
    }

    public static EdgeDB trueValue() {
        return new EdgeDB(true);
    }

    public static EdgeDB falseValue() {
        return new EdgeDB(true);
    }

    public EdgeDB filterNext(String edgeLabel, EdgeDB lhs, EdgeDB rhs) {
        ReflexiveLabelledMap<Node, Node, String> newEdges = new ReflexiveLabelledMap<>();
        Set<Node> lhsSet = lhs.edges.getKeySet();
        Set<Node> rhsSet = rhs.edges.getValueSet();
        lhsSet.forEach(node -> edges.getValues(node).forEach(objects -> {
            if(objects.get1().equals(edgeLabel) && rhsSet.contains(objects.get2())) {
                newEdges.addPair(objects.get2(), objects.get2(), "self");
            }
        }));
        return new EdgeDB(newEdges, threadNodeMapping, varNodeMapping, lastNode, true);
    }

    public EdgeDB filterSuccessors(String edgeLabel, EdgeDB lhs, EdgeDB rhs) {
        ReflexiveLabelledMap<Node, Node, String> newEdges = new ReflexiveLabelledMap<>();
        ReflexiveLabelledMap<Node, Node, String> lhsEdges = lhs.edges;
        Set<Node> rhsSet = rhs.edges.getValueSet();
        for (Node node : lhsEdges.getKeySet()) {
            dfs(lhsEdges, node, edgeLabel, node1 -> {
                if(rhsSet.contains(node1)) {
                    newEdges.addPair(node1, node1, "self");
                }
            });
        }
        return new EdgeDB(newEdges, threadNodeMapping, varNodeMapping, lastNode, true);
    }

    private void dfs(ReflexiveLabelledMap<Node, Node, String> edges, Node node, String edgeLabel, Consumer<Node> filter) {
        for (Tuple2<String, Node> value : edges.getValues(node)) {
            if(value.get1().equals(edgeLabel)) {
                dfs(edges, value.get2(), edgeLabel, filter);
            }
            filter.accept(value.get2());
        }
    }

    public Set<Variable> getVars() {
        return varNodeMapping.keySet();
    }

    public Set<Thread> getThreads() {
        return threadNodeMapping.keySet();
    }

    public Set<Node> getNodes() {
        Set<Node> ret = new HashSet<>(edges.getKeySet());
        ret.addAll(edges.getValueSet());
        return ret;
    }

    public EdgeDB union(EdgeDB apply) {
        ReflexiveLabelledMap<Node, Node, String> newEdges = new ReflexiveLabelledMap<>();
        if(onlyNodesAreValid == apply.onlyNodesAreValid) {
            for (Node node : edges.getKeySet()) {
                for (Tuple2<String, Node> value : edges.getValues(node)) {
                    newEdges.addPair(node, value.get2(), value.get1());
                }
            }
            for (Node node : apply.edges.getKeySet()) {
                for (Tuple2<String, Node> value : apply.edges.getValues(node)) {
                    newEdges.addPair(node, value.get2(), value.get1());
                }
            }
        }
        else {
            throw new UnsupportedOperationException("Trying to unionize set of nodes and edges!");
        }
        return new EdgeDB(newEdges, threadNodeMapping, varNodeMapping, lastNode, onlyNodesAreValid || apply.onlyNodesAreValid);
    }

    public EdgeDB intersect(EdgeDB apply) {
        ReflexiveLabelledMap<Node, Node, String> newEdges = new ReflexiveLabelledMap<>();
        if(onlyNodesAreValid && apply.onlyNodesAreValid) {
            Set<Node> myNodes = getNodes();
            Set<Node> otherNodes = apply.getNodes();
            for (Node myNode : myNodes) {
                if(otherNodes.contains(myNode)) {
                    newEdges.addPair(myNode, myNode, "self");
                }
            }
        }
        else if(!onlyNodesAreValid && !apply.onlyNodesAreValid) {
            for (Node node : edges.getKeySet()) {
                for (Tuple2<String, Node> value : edges.getValues(node)) {
                    if (apply.edges.getValues(node).contains(value)) {
                        newEdges.addPair(node, value.get2(), value.get1());
                    }
                }
            }
        }
        else {
            throw new UnsupportedOperationException("Trying to intersect set of nodes and edges!");
        }
        return new EdgeDB(newEdges, threadNodeMapping, varNodeMapping, lastNode, onlyNodesAreValid || apply.onlyNodesAreValid);
    }

    public EdgeDB minus(EdgeDB apply) {
        ReflexiveLabelledMap<Node, Node, String> newEdges = new ReflexiveLabelledMap<>();
        if(onlyNodesAreValid && apply.onlyNodesAreValid) {
            Set<Node> myNodes = getNodes();
            Set<Node> otherNodes = apply.getNodes();
            for (Node myNode : myNodes) {
                if(!otherNodes.contains(myNode)) {
                    newEdges.addPair(myNode, myNode, "self");
                }
            }
        }
        else if(!onlyNodesAreValid && !apply.onlyNodesAreValid) {
            for (Node node : edges.getKeySet()) {
                for (Tuple2<String, Node> value : edges.getValues(node)) {
                    if (!apply.edges.getValues(node).contains(value)) {
                        newEdges.addPair(node, value.get2(), value.get1());
                    }
                }
            }
        }
        else {
            throw new UnsupportedOperationException("Trying to subtract set of nodes and edges!");
        }
        return new EdgeDB(newEdges, threadNodeMapping, varNodeMapping, lastNode, onlyNodesAreValid || apply.onlyNodesAreValid);
    }

    public EdgeDB multiply(EdgeDB apply, String label) {
        if(onlyNodesAreValid && apply.onlyNodesAreValid) {
            ReflexiveLabelledMap<Node, Node, String> newEdges = new ReflexiveLabelledMap<>();
            Set<Node> lhsNodes = getNodes();
            Set<Node> rhsNodes = apply.getNodes();
            for(Node lhsNode : lhsNodes) {
                for(Node rhsNode : rhsNodes) {
                    newEdges.addPair(lhsNode, rhsNode, label);
                }
            }
            return new EdgeDB(newEdges, threadNodeMapping, varNodeMapping, lastNode, false);
        }
        else {
            throw new UnsupportedOperationException("Trying to multiply edges!");
        }
    }

    public EdgeDB filterNamed(String text) {
        ReflexiveLabelledMap<Node, Node, String> newEdges = new ReflexiveLabelledMap<>();
        if(text.equals(text.toUpperCase())) {
            switch(text) {
                case "W" : getNodes().stream().filter(node -> node instanceof Write).forEach(node -> newEdges.addPair(node, node, "self")); break;
                case "R" : getNodes().stream().filter(node -> node instanceof Read).forEach(node -> newEdges.addPair(node, node, "self")); break;
                case "F" : getNodes().stream().filter(node -> node instanceof Fence).forEach(node -> newEdges.addPair(node, node, "self")); break;
                case "A" : getNodes().forEach(node -> newEdges.addPair(node, node, "self")); break;
                default: throw new UnsupportedOperationException("Cannot retrieve named node " + text);
            }
            return new EdgeDB(newEdges, threadNodeMapping, varNodeMapping, lastNode, true);
        }
        else if(!onlyNodesAreValid){
            for (Node node : edges.getKeySet()) {
                for (Tuple2<String, Node> value : edges.getValues(node)) {
                    if(value.get1().equals(text)) {
                        newEdges.addPair(node, value.get2(), value.get1());
                    }
                }
            }
            return new EdgeDB(newEdges, threadNodeMapping, varNodeMapping, lastNode, false);
        }
        else {
            throw new UnsupportedOperationException("Cannot filter graph containing only nodes by edge label!");
        }
    }

    public EdgeDB filterNode(Node node) {
        ReflexiveLabelledMap<Node, Node, String> newEdges = new ReflexiveLabelledMap<>();
        if(getNodes().contains(node)) {
            newEdges.addPair(node, node, "self");
        }
        return new EdgeDB(newEdges, threadNodeMapping, varNodeMapping, node, true);
    }

    public EdgeDB filterThread(Thread thread) {
        ReflexiveLabelledMap<Node, Node, String> newEdges = new ReflexiveLabelledMap<>();
        Set<Node> nodes = getNodes();
        for (Node node : threadNodeMapping.get(thread)) {
            if(nodes.contains(node)) {
                newEdges.addPair(node, node, "self");
            }
        }
        return new EdgeDB(newEdges, threadNodeMapping, varNodeMapping, lastNode, true);
    }

    public EdgeDB filterVar(Variable var) {
        ReflexiveLabelledMap<Node, Node, String> newEdges = new ReflexiveLabelledMap<>();
        Set<Node> nodes = getNodes();
        for (Node node : varNodeMapping.get(var)) {
            if(nodes.contains(node)) {
                newEdges.addPair(node, node, "self");
            }
        }
        return new EdgeDB(newEdges, threadNodeMapping, varNodeMapping, lastNode, true);
    }

    public EdgeDB filterNew() {
        return filterNode(lastNode);
    }

    public EdgeDB and(EdgeDB apply) {
        if(onlyLogicalValue && apply.onlyLogicalValue) {
            return new EdgeDB(truth && apply.truth);
        }
        else {
            throw new UnsupportedOperationException("Trying to use boolean logic on non-boolean valued items!");
        }
    }

    public EdgeDB or(EdgeDB apply) {
        if(onlyLogicalValue && apply.onlyLogicalValue) {
            return new EdgeDB(truth || apply.truth);
        }
        else {
            throw new UnsupportedOperationException("Trying to use boolean logic on non-boolean valued items!");
        }
    }

    public EdgeDB not() {
        if(onlyLogicalValue) {
            return new EdgeDB(!truth);
        }
        else {
            throw new UnsupportedOperationException("Trying to use boolean logic on non-boolean valued items!");
        }
    }

    public EdgeDB imply(EdgeDB apply) {
        if(onlyLogicalValue && apply.onlyLogicalValue) {
            return new EdgeDB(!truth || apply.truth);
        }
        else {
            throw new UnsupportedOperationException("Trying to use boolean logic on non-boolean valued items!");
        }
    }

    private boolean checkCycles(Set<Node> nodes, Node node) {
        if(nodes.contains(node)) return true;
        nodes.add(node);
        for (Tuple2<String, Node> value : edges.getValues(node)) {
            if(checkCycles(nodes, value.get2())) return true;
        }
        nodes.remove(node);
        return false;
    }

    public EdgeDB isAcyclic() {
        for (Node node : edges.getKeySet()) {
            if(checkCycles(new HashSet<>(), node)) return falseValue();
        }
        return trueValue();
    }

    public EdgeDB isIrreflexive() {
        checkState(!onlyLogicalValue);
        for (Node node : edges.getKeySet()) {
            for (Tuple2<String, Node> value : edges.getValues(node)) {
                for (Tuple2<String, Node> edgesValue : edges.getValues(value.get2())) {
                    if(edgesValue.get2() == node) return falseValue();
                }
            }
        }
        return trueValue();
    }

    public EdgeDB isEmpty() {
        checkState(!onlyLogicalValue);
        return getNodes().isEmpty() ? trueValue() : falseValue();
    }

    public boolean isOk() {
        checkState(onlyLogicalValue);
        return truth;
    }

}
