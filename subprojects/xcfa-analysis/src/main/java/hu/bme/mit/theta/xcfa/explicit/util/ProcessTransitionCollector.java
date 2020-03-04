package hu.bme.mit.theta.xcfa.explicit.util;

import hu.bme.mit.theta.xcfa.XCFA;
import hu.bme.mit.theta.xcfa.XCFA.Process.Procedure;
import hu.bme.mit.theta.xcfa.simulator.ProcedureData;
import hu.bme.mit.theta.xcfa.simulator.Transition;

import java.util.Collection;
import java.util.HashSet;

// collects all transitions from a given process
public class ProcessTransitionCollector {
    public static Collection<Transition> getAllTransitionsByProcess(XCFA.Process process) {
        Collection<Transition> result = new HashSet<>();
        for (Procedure p: process.getProcedures()) {
            var locations = ProcedureData.getInstance(p, process).listAllLocations();
            for (ProcedureData.LocationWrapper loc : locations) {
                result.addAll(loc.getTransitions());
            }
        }
        return result;
    }
}
