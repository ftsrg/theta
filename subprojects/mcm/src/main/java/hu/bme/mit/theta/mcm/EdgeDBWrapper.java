package hu.bme.mit.theta.mcm;

import hu.bme.mit.theta.mcm.graph.EdgeDB;
import hu.bme.mit.theta.mcm.graph.classification.nodes.Fence;
import hu.bme.mit.theta.mcm.graph.classification.nodes.Node;
import hu.bme.mit.theta.mcm.graph.classification.nodes.Read;
import hu.bme.mit.theta.mcm.graph.classification.nodes.Write;

import java.util.Set;
import java.util.function.Predicate;

public class EdgeDBWrapper {
    private final EdgeDB edgeDB;
    private final Predicate<Object> shouldModify;
    private final Predicate<EdgeDB> constraint;

    public EdgeDBWrapper(EdgeDB edgeDB, Set<String> modifications, Predicate<EdgeDB> constraint) {
        this.edgeDB = edgeDB;
        Predicate<Object> base = o -> false;
        for (String modification : modifications) {
            switch (modification) {
                case "W":
                    base = base.or(o -> o instanceof Write);
                    break;
                case "R":
                    base = base.or(o -> o instanceof Read);
                    break;
                case "F":
                    base = base.or(o -> o instanceof Fence);
                    break;
                case "A":
                    base = base.or(o -> o instanceof Write).or(o -> o instanceof Read).or(o -> o instanceof Fence);
                    break;
                default:
                    base = base.or(o -> o instanceof String && o.equals(modification));
            }
        }
        this.shouldModify = base;
        this.constraint = constraint;
    }

    public void addEdge(Node source, Node target, String label, boolean replaceSource, boolean replaceTarget) {
        if (shouldModify.test(source) || shouldModify.test(target) || shouldModify.test(label)) {
            edgeDB.addEdge(source, target, label, replaceSource, replaceTarget);
        }
    }
}
