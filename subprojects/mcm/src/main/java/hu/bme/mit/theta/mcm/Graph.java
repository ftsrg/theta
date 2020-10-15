package hu.bme.mit.theta.mcm;

import hu.bme.mit.theta.common.Tuple2;
import hu.bme.mit.theta.mcm.graphfilter.interfaces.MemoryAccess;

import java.util.*;
import java.util.stream.Collectors;

import static com.google.common.base.Preconditions.checkState;

public class Graph {
    private final Map<MemoryAccess, Set<Tuple2<MemoryAccess, Boolean>>> forward;
    private final Map<MemoryAccess, Set<Tuple2<MemoryAccess, Boolean>>> reverse;

    private Graph() {
        forward = new HashMap<>();
        reverse = new HashMap<>();
    }

    private Graph(Map<MemoryAccess, Set<Tuple2<MemoryAccess, Boolean>>> forward, Map<MemoryAccess, Set<Tuple2<MemoryAccess, Boolean>>> reverse) {
        this.forward = new HashMap<>();
        this.reverse = new HashMap<>();
        forward.forEach((MemoryAccess, tuple2s) -> this.forward.put(MemoryAccess, new HashSet<>(tuple2s)));
        reverse.forEach((MemoryAccess, tuple2s) -> this.reverse.put(MemoryAccess, new HashSet<>(tuple2s)));
    }

    public static  Graph empty() {
        return new Graph();
    }

    public Graph duplicate() {
        return new Graph(forward, reverse);
    }

    public void addEdge(MemoryAccess source, MemoryAccess target, boolean isFinal) {
        forward.putIfAbsent(source, new HashSet<>());
        reverse.putIfAbsent(target, new HashSet<>());
        forward.get(source).add(Tuple2.of(target, isFinal));
        reverse.get(target).add(Tuple2.of(source, isFinal));
    }

    public void removeEdge(MemoryAccess source, MemoryAccess target) {
        if(forward.containsKey(source) && reverse.containsKey(target)) {
            forward.get(source).remove(Tuple2.of(target, false));
            reverse.get(target).remove(Tuple2.of(source, false));
            forward.get(source).remove(Tuple2.of(target, true));
            reverse.get(target).remove(Tuple2.of(source, true));
        }
    }

    public boolean isDisconnected(MemoryAccess t) {
        return reverse.getOrDefault(t, new HashSet<>()).size() == 0 && forward.getOrDefault(t, new HashSet<>()).size() == 0;
    }

    public void markFinal(MemoryAccess source, MemoryAccess target) {
        checkState(exists(source, target), "Edge does not exist.");
        Set<Tuple2<MemoryAccess, Boolean>> forwardList = forward.get(source);
        if(forwardList.contains(Tuple2.of(target, false))) {
            Set<Tuple2<MemoryAccess, Boolean>> reverseList = reverse.get(target);
            forwardList.remove(Tuple2.of(target, false));
            forwardList.add(Tuple2.of(target, true));
            reverseList.remove(Tuple2.of(source, false));
            reverseList.add(Tuple2.of(source, true));
        }
    }

    public boolean exists(MemoryAccess source, MemoryAccess target) {
        return  forward.get(source).contains(Tuple2.of(target, true)) ||
                forward.get(source).contains(Tuple2.of(target, false));
    }

    public boolean isAcyclic() {
        for (MemoryAccess memoryAccess : forward.keySet()) {
            if(isCyclic(new HashSet<>(), memoryAccess)) return false;
        }
        return true;
    }

    private boolean isCyclic(Set<MemoryAccess> path, MemoryAccess tail) {
        path.add(tail);
        for (Tuple2<MemoryAccess, Boolean> tuple2 : forward.getOrDefault(tail, Set.of())) {
            if(path.contains(tuple2.get1())) return true;
            else if(isCyclic(path, tuple2.get1())) return true;
        }
        path.remove(tail);
        return false;
    }

    public boolean isEmpty() {
        for (Map.Entry<MemoryAccess, Set<Tuple2<MemoryAccess, Boolean>>> nodeSetEntry : forward.entrySet()) {
            if(nodeSetEntry.getValue().size() > 0) return false;
        }
        return true;
    }

    public boolean isIrreflexive() {
        for (Map.Entry<MemoryAccess, Set<Tuple2<MemoryAccess, Boolean>>> nodeSetEntry : forward.entrySet()) {
            if(nodeSetEntry.getValue().contains(Tuple2.of(nodeSetEntry.getKey(), true)) ||
               nodeSetEntry.getValue().contains(Tuple2.of(nodeSetEntry.getKey(), false))) {
                return false;
            }
        }
        return true;


    }

    public Set<MemoryAccess> extractTargetNodes() {
        return reverse.keySet().stream().filter(t -> !isDisconnected(t)).collect(Collectors.toSet());
    }

    public Set<MemoryAccess> extractSourceNodes() {
        return forward.keySet().stream().filter(t -> !isDisconnected(t)).collect(Collectors.toSet());

    }

    public Graph minus(Graph graph) {
        Graph retGraph = duplicate();
        graph.forward.forEach((t, tuple2s) -> tuple2s.forEach(tuple2 -> {
            retGraph.removeEdge(t, tuple2.get1());
        }));
        return retGraph;
    }

    public Graph section(Graph graph) {
        Graph retGraph = empty();
        graph.forward.forEach((t, tuple2s) -> tuple2s.forEach(tuple2 -> {
            if(exists(t, tuple2.get1())) {
                retGraph.addEdge(t, tuple2.get1(), tuple2.get2());
            }
        }));
        return retGraph;
    }

    public Graph union(Graph graph) {
        Graph retGraph = duplicate();
        graph.forward.forEach((t, tuple2s) -> tuple2s.forEach(tuple2 -> {
            retGraph.addEdge(t, tuple2.get1(), tuple2.get2());
        }));
        return retGraph;
    }

    public boolean isFinal() {
        return false;
    }

    public String printGraph() {
        StringBuilder stringBuilder = new StringBuilder("digraph G{\n");
        forward.forEach((memoryAccess, tuple2s) -> {
            for (Tuple2<MemoryAccess, Boolean> tuple2 : tuple2s) {
                stringBuilder.append(memoryAccess.toString()).append(" -> ").append(tuple2.get1()).append("\n");
            }
        });
        return stringBuilder.append("}").toString();
    }
}
