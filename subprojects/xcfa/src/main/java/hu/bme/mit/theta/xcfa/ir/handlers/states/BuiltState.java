package hu.bme.mit.theta.xcfa.ir.handlers.states;

import hu.bme.mit.theta.xcfa.model.XCFA;
import hu.bme.mit.theta.xcfa.model.XcfaProcedure;
import hu.bme.mit.theta.xcfa.model.XcfaProcess;

import java.util.HashMap;
import java.util.Map;

import static com.google.common.base.Preconditions.checkState;

public class BuiltState {
    private XCFA xcfa;
    private Map<String, XcfaProcess> processes;
    private Map<String, XcfaProcedure> procedures;

    public BuiltState() {
        processes = new HashMap<>();
        procedures = new HashMap<>();
    }

    public XCFA getXcfa() {
        checkState(xcfa != null, "XCFA has not been built yet");
        return xcfa;
    }

    public Map<String, XcfaProcess> getProcesses() {
        return processes;
    }

    public Map<String, XcfaProcedure> getProcedures() {
        return procedures;
    }

    public void setProcedures(Map<String, XcfaProcedure> procedures) {
        this.procedures = procedures;
    }

    public void setProcesses(Map<String, XcfaProcess> processes) {
        this.processes = processes;
    }

    public void setXcfa(XCFA xcfa) {
        this.xcfa = xcfa;
    }
}
