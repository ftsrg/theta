package hu.bme.mit.theta.mcm;

import hu.bme.mit.theta.mcm.graphfilter.Filter;
import hu.bme.mit.theta.mcm.graphfilter.interfaces.MemoryAccess;

import java.util.Set;
import java.util.Stack;

public class EmptyConstraint extends Constraint {
    public GraphOrNodeSet getLast() {
        return last;
    }

    private GraphOrNodeSet last;

    public EmptyConstraint(Filter filter, boolean not, String name) {
        super(filter, not, name);
    }

    public EmptyConstraint(Filter duplicate, boolean not, String name, GraphOrNodeSet last) {
        super(duplicate, not, name);
        this.last = last;
    }

    public boolean checkMk(MemoryAccess source, MemoryAccess target, String label, boolean isFinal) {
        Set<GraphOrNodeSet> resultSet = filter.filterMk(source, target, label, isFinal);
        for (GraphOrNodeSet result : resultSet) {
            last = result;
            if(result.isGraph()) {
                if(not && result.getGraph().isEmpty()) return false;
                else if(!not && !result.getGraph().isEmpty()) return false;
            }
            else {
                if(not && result.getNodeSet().isEmpty()) return false;
                else if(!not && !result.getNodeSet().isEmpty()) return false;
            }
        }
        return true;
    }
    public boolean checkRm(MemoryAccess source, MemoryAccess target, String label) {
        Set<GraphOrNodeSet> resultSet = filter.filterRm(source, target, label);
        for (GraphOrNodeSet result : resultSet) {
            last = result;
            if(result.isGraph()) {
                if(not && result.getGraph().isEmpty()) return false;
                else if(!not && !result.getGraph().isEmpty()) return false;
            }
            else {
                if(not && result.getNodeSet().isEmpty()) return false;
                else if(!not && !result.getNodeSet().isEmpty()) return false;
            }
        }
        return true;
    }

    @Override
    public Constraint duplicate() {
        return new EmptyConstraint(filter.duplicate(new Stack<>(), new Stack<>(), new Stack<>()), not, name, last);
    }
}
