package hu.bme.mit.theta.mcm;

import hu.bme.mit.theta.common.Tuple2;
import hu.bme.mit.theta.mcm.graphfilter.interfaces.MemoryAccess;
import hu.bme.mit.theta.mcm.graphfilter.interfaces.Write;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

public class MCM {
    private boolean violated;

    private final Set<Constraint> constraints;
    private Constraint violator;

    public MCM() {
        constraints = new HashSet<>();
    }

    public MCM(boolean violated, Set<Constraint> constraints, Constraint violator) {
        this.violated = violated;
        this.constraints = new HashSet<>();
        for (Constraint constraint : constraints) {
            Constraint duplicated = constraint.duplicate();
            this.constraints.add(duplicated);
            if(violator == constraint) this.violator = duplicated;
        }
    }

    public <T extends MemoryAccess> void fromEdges(Set<? extends Write> initialWrites, Map<T, Set<Tuple2<T, String>>> edges) {
        Map<T, Set<Tuple2<T, String>>> usedEdges = new HashMap<>();
        for (Write initialWrite : initialWrites) {
            addEdge(initialWrite, usedEdges, edges);
        }
    }

    private <T extends MemoryAccess> void addEdge(MemoryAccess memoryAccess, Map<T, Set<Tuple2<T, String>>> usedEdges, Map<T, Set<Tuple2<T, String>>> edges) {
        usedEdges.putIfAbsent((T) memoryAccess, new HashSet<>());
        for (Tuple2<T, String> objects : edges.getOrDefault(memoryAccess, new HashSet<>())) {
            if(!usedEdges.get(memoryAccess).contains(objects)) {
                usedEdges.get(memoryAccess).add(objects);
                checkMk(memoryAccess, objects.get1(), objects.get2(), true);
                addEdge(objects.get1(), usedEdges, edges);
            }
        }
    }

    public void addConstraint(Constraint g) {
        constraints.add(g);
    }

    public Set<Constraint> getConstraints() {
        return constraints;
    }

    public void checkMk(MemoryAccess source, MemoryAccess target, String label, boolean isFinal) {
        for (Constraint constraint : constraints) {
            if(!constraint.checkMk(source, target, label, isFinal)) {
                violated = true;
                violator = constraint;
                return;
            }
        }
        violated = false;
    }

    public void checkRm(MemoryAccess source, MemoryAccess target, String label) {
        for (Constraint constraint : constraints) {
            if(!constraint.checkRm(source, target, label)) {
                violated = true;
                return;
            }
        }
        violated = false;
    }

    public boolean isViolated() {
        return violated;
    }

    public MCM duplicate() {
        return new MCM(violated, constraints, violator);
    }

    public Constraint getViolator() {
        return violator;
    }
}
