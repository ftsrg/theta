package hu.bme.mit.theta.xcfa.analysis.stateless;

import hu.bme.mit.theta.core.model.MutableValuation;
import hu.bme.mit.theta.xcfa.XCFA;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

public class State {

    private final MutableValuation mutableValuation;
    private final XCFA xcfa;
    private final Map<XCFA.Process, List<XCFA.Process.Procedure>> callStacks;
    private final Map<XCFA.Process, XCFA.Process.Procedure.Location> currentLoc;

    public State(final XCFA xcfa) {
        this.mutableValuation = new MutableValuation();
        this.xcfa = xcfa;
        this.callStacks = new HashMap<>();
        this.currentLoc = new HashMap<>();
        for(XCFA.Process process : xcfa.getProcesses()) {
            this.callStacks.put(process, new ArrayList<>());
            this.currentLoc.put(process, process.getMainProcedure().getInitLoc());
        }
    }

    private State(
            final MutableValuation mutableValuation,
            final XCFA xcfa,
            final Map<XCFA.Process, List<XCFA.Process.Procedure>> callStacks,
            final Map<XCFA.Process, XCFA.Process.Procedure.Location> currentLoc
            ) {
        this.mutableValuation = MutableValuation.copyOf(mutableValuation);
        this.xcfa = xcfa;
        this.callStacks = new HashMap<>();
        for(XCFA.Process process : xcfa.getProcesses()) {
            this.callStacks.put(process, List.copyOf(callStacks.get(process)));
        }
        this.currentLoc =  Map.copyOf(currentLoc);
    }

    public static State copyOf(State state) {
        return new State(state.mutableValuation, state.xcfa, state.callStacks, state.currentLoc);
    }
}
