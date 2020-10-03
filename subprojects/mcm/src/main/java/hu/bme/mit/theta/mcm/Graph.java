package hu.bme.mit.theta.mcm;

import hu.bme.mit.theta.common.Tuple2;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import static com.google.common.base.Preconditions.checkState;

public class Graph<T> {
    private final Map<T, Node> LUT;
    private final Map<Node, Set<Tuple2<Node, Boolean>>> forward;
    private final Map<Node, Set<Tuple2<Node, Boolean>>> reverse;
    private final boolean checkAcylic;
    private boolean acyclic;

    private Graph(boolean checkAcylic) {
        acyclic = false;
        this.checkAcylic = checkAcylic;
        LUT = new HashMap<>();
        forward = new HashMap<>();
        reverse = new HashMap<>();
    }

    private Graph(Map<T, Node> lut, Map<Node, Set<Tuple2<Node, Boolean>>> forward, Map<Node, Set<Tuple2<Node, Boolean>>> reverse, boolean checkAcylic, boolean acyclic) {
        this.LUT = lut;
        this.forward = new HashMap<>();
        this.reverse = new HashMap<>();
        forward.forEach((node, tuple2s) -> this.forward.put(node, new HashSet<>(tuple2s)));
        reverse.forEach((node, tuple2s) -> this.reverse.put(node, new HashSet<>(tuple2s)));
        this.checkAcylic = checkAcylic;
        this.acyclic = acyclic;
    }

    public static <T> Graph<T> create(boolean checkAcylic) {
        return new Graph<T>(checkAcylic);
    }

    public Graph<T> duplicate() {
        return new Graph<T>(LUT, forward, reverse, checkAcylic, acyclic);
    }

    public void addEdge(T source, T target, boolean isFinal) {
        checkState(!exists(source, target), "Edge already exists! Use the replace/markFinal functions instead.");
        forward.get(getNode(source)).add(Tuple2.of(getNode(target), isFinal));
        reverse.get(getNode(target)).add(Tuple2.of(getNode(source), isFinal));
        if(checkAcylic && acyclic) {
            remainsAcyclic(getNode(source), getNode(target));
        }
    }

    public void removeEdge(T source, T target) {
        checkState(forward.get(getNode(source)).contains(Tuple2.of(getNode(target), false)), "Edge does not exist or is marked final.");
        forward.get(getNode(source)).remove(Tuple2.of(getNode(target), false));
        reverse.get(getNode(target)).remove(Tuple2.of(getNode(source), false));
        if(checkAcylic && !acyclic) {
            becomesAcyclic(getNode(source), getNode(target));
        }
    }

    public boolean isDisconnected(T node) {
        return reverse.get(getNode(node)).size() == 0 && forward.get(getNode(node)).size() == 0;
    }

    public void replaceEdge(T origSource, T origTarget, T newSource, T newTarget, boolean isFinal) {
        removeEdge(origSource, origTarget);
        addEdge(newSource, newTarget, isFinal);
    }

    public void markFinal(T source, T target) {
        checkState(exists(source, target), "Edge does not exist.");
        Set<Tuple2<Node, Boolean>> forwardList = forward.get(getNode(source));
        if(forwardList.contains(Tuple2.of(getNode(target), false))) {
            Set<Tuple2<Node, Boolean>> reverseList = reverse.get(getNode(target));
            forwardList.remove(Tuple2.of(getNode(target), false));
            forwardList.add(Tuple2.of(getNode(target), true));
            reverseList.remove(Tuple2.of(getNode(source), false));
            reverseList.add(Tuple2.of(getNode(source), true));
        }
    }

    public boolean exists(T source, T target) {
        return  forward.get(getNode(source)).contains(Tuple2.of(getNode(target), true)) ||
                forward.get(getNode(source)).contains(Tuple2.of(getNode(target), false));
    }

    public boolean isAcyclic() {
        return acyclic;
    }

    public boolean isEmpty() {
        for (Map.Entry<Node, Set<Tuple2<Node, Boolean>>> nodeSetEntry : forward.entrySet()) {
            if(nodeSetEntry.getValue().size() > 0) return false;
        }
        return true;
    }

    public boolean isIrreflexive() {
        for (Map.Entry<Node, Set<Tuple2<Node, Boolean>>> nodeSetEntry : forward.entrySet()) {
            if(nodeSetEntry.getValue().contains(Tuple2.of(nodeSetEntry.getKey(), true)) ||
               nodeSetEntry.getValue().contains(Tuple2.of(nodeSetEntry.getKey(), false))) {
                return false;
            }
        }
        return true;


    }

    private Node getNode(T nodeProxy) {
        if(LUT.containsKey(nodeProxy)) {
            return LUT.get(nodeProxy);
        }
        Node ret;
        LUT.put(nodeProxy, ret = new Node());
        forward.put(ret, new HashSet<>());
        reverse.put(ret, new HashSet<>());
        return ret;
    }


    private void remainsAcyclic(Node source, Node target) {
        acyclic = false;
    }

    private void becomesAcyclic(Node source, Node target) {
        acyclic = true;
    }

    public Graph<T> union(Graph<T> graph) {
        return null;
    }

    public Set<T> extractTargetNodes() {
        return null;
    }

    public Set<T> extractSourceNodes() {
        return null;
    }

    public Graph<T> minus(Graph<T> graph) {
        return null;
    }

    public Graph<T> section(Graph<T> graph) {
        return null;
    }


    private static class Node {

    }
}
