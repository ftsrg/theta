package hu.bme.mit.theta.xcfa.simulator;

import hu.bme.mit.theta.core.model.MutableValuation;
import hu.bme.mit.theta.core.utils.VarIndexing;
import hu.bme.mit.theta.xcfa.XCFA;

import java.util.ArrayList;
import java.util.List;

class RuntimeState {
    List<ProcessState> processStates;
    XCFA xcfa;
    Simulator simulator;
    MutableValuation valuation;
    VarIndexing vars;

    public RuntimeState(Simulator simulator, XCFA xcfa) {
        valuation = new MutableValuation();
        vars = VarIndexing.builder(0).build();
        this.simulator = simulator;
        this.xcfa = xcfa;
        List<XCFA.Process> procs = xcfa.getProcesses();
        processStates = new ArrayList<>();
        for (XCFA.Process proc : procs) {
            processStates.add(new ProcessState(this, proc));
        }
    }

    /**
     * Steps in a deterministic way
     */
    public boolean step() {
        for (ProcessState state : processStates) {
            if (state.step()) {
                return true;
            }
        }
        return false;
    }
}
