package hu.bme.mit.theta.mcm;

import hu.bme.mit.theta.mcm.graphfilter.Filter;
import hu.bme.mit.theta.mcm.graphfilter.interfaces.MemoryAccess;

import java.util.Set;

public class AcyclicConstraint extends Constraint {
    public AcyclicConstraint(Filter filter, boolean not) {
        super(filter, not);
    }

    public AcyclicResult checkMk(MemoryAccess source, MemoryAccess target, String label, boolean isFinal) {
        Set<GraphOrNodeSet> resultSet = filter.filterMk(source, target, label, isFinal);
        for (GraphOrNodeSet result : resultSet) {
            if(result.isGraph()) {
                if(not && result.getGraph().isAcyclic()) return new AcyclicResult();
                else if(!not && !result.getGraph().isAcyclic()) return new CyclicResult(result.getGraph(), result.getGraph().isFinal());
            }
            else {
                throw new UnsupportedOperationException("Cannot check for acyclicity in a set!");
            }
        }
        Graph ret;
        return not ? new CyclicResult(ret = resultSet.iterator().next().getGraph(), ret.isFinal()) : new AcyclicResult();
    }
    public AcyclicResult checkRm(MemoryAccess source, MemoryAccess target, String label) {
        Set<GraphOrNodeSet> resultSet = filter.filterRm(source, target, label);
        for (GraphOrNodeSet result : resultSet) {
            if(result.isGraph()) {
                if(not && result.getGraph().isAcyclic()) return new AcyclicResult();
                else if(!not && !result.getGraph().isAcyclic()) return new CyclicResult(result.getGraph(), result.getGraph().isFinal());
            }
            else {
                throw new UnsupportedOperationException("Cannot check for acyclicity in a set!");
            }
        }
        Graph ret;
        return not ? new CyclicResult(ret = resultSet.iterator().next().getGraph(), ret.isFinal()) : new AcyclicResult();
    }
}
