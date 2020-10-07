package hu.bme.mit.theta.mcm;

import hu.bme.mit.theta.mcm.graphfilter.Filter;
import hu.bme.mit.theta.mcm.graphfilter.interfaces.MemoryAccess;

import java.util.Set;

public class EmptyConstraint extends Constraint {
    public EmptyConstraint(Filter filter, boolean not) {
        super(filter, not);
    }

    public EmptyResult checkMk(MemoryAccess source, MemoryAccess target, String label, boolean isFinal) {
        Set<GraphOrNodeSet> resultSet = filter.filterMk(source, target, label, isFinal);
        for (GraphOrNodeSet result : resultSet) {
            if(result.isGraph()) {
                if(result.getGraph().isEmpty()) return new EmptyResult();
                else return new NonEmptyResult(result, result.getGraph().isFinal());
            }
            else {
                if(result.getNodeSet().isEmpty()) return new EmptyResult();
                else return new NonEmptyResult(result, false); // TODO
            }
        }
        return new EmptyResult();
    }
    public EmptyResult checkRm(MemoryAccess source, MemoryAccess target, String label) {
        Set<GraphOrNodeSet> resultSet = filter.filterRm(source, target, label);
        for (GraphOrNodeSet result : resultSet) {
            if(result.isGraph()) {
                if(not && result.getGraph().isEmpty()) return new EmptyResult();
                else if(!not && !result.getGraph().isEmpty()) return new NonEmptyResult(result, result.getGraph().isFinal());
            }
            else {
                if(not && result.getNodeSet().isEmpty()) return new EmptyResult();
                else if(!not && !result.getNodeSet().isEmpty()) return new NonEmptyResult(result, result.getGraph().isFinal());
            }
        }
        return not ? new NonEmptyResult(resultSet.iterator().next(), false) : new EmptyResult();
    }
}
