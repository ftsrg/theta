package hu.bme.mit.theta.mcm;

import hu.bme.mit.theta.mcm.graphfilter.Filter;
import hu.bme.mit.theta.mcm.graphfilter.interfaces.MemoryAccess;

import java.util.Set;
import java.util.Stack;

public class AcyclicConstraint extends Constraint {
    private Graph last;
    public AcyclicConstraint(Filter filter, boolean not, String name) {
        super(filter, not, name);
    }

    public AcyclicConstraint(Filter duplicate, boolean not, String name, Graph last) {
        super(duplicate, not, name);
        this.last = last;
    }

    public boolean checkMk(MemoryAccess source, MemoryAccess target, String label, boolean isFinal) {
        Set<GraphOrNodeSet> resultSet = filter.filterMk(source, target, label, isFinal);
        for (GraphOrNodeSet result : resultSet) {
            if(result.isGraph()) {
                last = result.getGraph();
                if(not && result.getGraph().isAcyclic()) return false;
                else if(!not && !result.getGraph().isAcyclic()) return false;
            }
            else {
                throw new UnsupportedOperationException("Cannot check for acyclicity in a set!");
            }
        }
        return true;
    }
    public boolean checkRm(MemoryAccess source, MemoryAccess target, String label) {
        Set<GraphOrNodeSet> resultSet = filter.filterRm(source, target, label);
        for (GraphOrNodeSet result : resultSet) {
            if(result.isGraph()) {
                last = result.getGraph();
                if(not && result.getGraph().isAcyclic()) return false;
                else if(!not && !result.getGraph().isAcyclic()) return false;
            }
            else {
                throw new UnsupportedOperationException("Cannot check for acyclicity in a set!");
            }
        }
        return true;
    }

    @Override
    public Constraint duplicate() {
        return new AcyclicConstraint(filter.duplicate(new Stack<>(), new Stack<>(), new Stack<>()), not, name, last);
    }
}
