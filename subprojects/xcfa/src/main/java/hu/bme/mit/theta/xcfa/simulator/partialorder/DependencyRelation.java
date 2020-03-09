package hu.bme.mit.theta.xcfa.simulator.partialorder;

import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.xcfa.simulator.ProcedureData.LeaveTransition;
import hu.bme.mit.theta.xcfa.simulator.ProcessTransition;
import hu.bme.mit.theta.xcfa.simulator.StmtTransition;
import hu.bme.mit.theta.xcfa.simulator.Transition;

import java.util.Collection;

/**
 * Returns a dependency relation Clarke's definition.
 * Independent:
 *   If a and b are enabled, then a is enabled after b is executed (and the other way around)
 *   If a and b are enabled, then executing them gives the same result in any order
 *
 * a,b,c are pairwise independent
 *  If a,b,c are enabled:
 *    b and c are enabled after executing a
 *    a,b,c and a,c,b are the same
 *    a,c are enabled after executing b
 *    after executing b and a, c is enabled
 *    executing a,b is the same as b,a -> c is enabled in both, and a,b,c is equivalent to b,a,c and a,c,b
 */
public class DependencyRelation {
    public static boolean depends(Transition t1, Collection<Transition> t2s) {
        for (Transition t2 : t2s) {
            if (depends(t1, t2))
                return true;
        }
        return false;
    }

    private static boolean stmtDepends(StmtTransition a, StmtTransition b) {
        Collection<VarDecl<?>> listBRW = b.getRWVars();
        Collection<VarDecl<?>> listAW = a.getWVars();
        // only R-W and W-W operations on same var is a problem, R-R are not dependent
        // TODO two increment operations are independent
        boolean hasIntersection = listAW.stream()
                .anyMatch(listBRW::contains);
        if (hasIntersection)
            return true;
        Collection<VarDecl<?>> listARW = a.getRWVars();
        Collection<VarDecl<?>> listBW = b.getWVars();
        hasIntersection = listBW.stream()
                .anyMatch(listARW::contains);
        return hasIntersection;
    }
    private static boolean processDepends(ProcessTransition a, ProcessTransition b) {
        if (a.getProcess() == b.getProcess())
            return true;
        if (a instanceof LeaveTransition)
            return false;
        if (b instanceof LeaveTransition)
            return false;
        if (a instanceof StmtTransition && b instanceof StmtTransition) {
            return stmtDepends((StmtTransition) a, (StmtTransition) b);
        }
        return true;
    }
    public static boolean depends(Transition a, Transition b) {
        if (a instanceof ProcessTransition && b instanceof ProcessTransition) {
            return processDepends((ProcessTransition)a, (ProcessTransition)b);
        }
        return true;
    }
}
