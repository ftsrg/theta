package hu.bme.mit.theta.xcfa.simulator;

import hu.bme.mit.theta.core.model.MutableValuation;
import hu.bme.mit.theta.core.utils.VarIndexing;
import hu.bme.mit.theta.xcfa.XCFA;

import java.util.*;

public class RuntimeState {
	private Map<XCFA.Process, ProcessState> processStates;
	XCFA xcfa;
	MutableValuation valuation;
	VarIndexing vars;

	public ProcessState getProcessState(XCFA.Process process) {
		return processStates.get(process);
	}

	public RuntimeState(XCFA xcfa) {
		valuation = new MutableValuation();
		vars = VarIndexing.builder(0).build();
		this.xcfa = xcfa;
		List<XCFA.Process> procs = xcfa.getProcesses();
		processStates = new HashMap<>();
		for (XCFA.Process proc : procs) {
			processStates.put(proc, new ProcessState(this, proc));
		}
	}

	public RuntimeState(RuntimeState toCopy) {
		valuation = MutableValuation.copyOf(toCopy.valuation);
		vars = toCopy.vars.transform().build();
		xcfa = toCopy.xcfa; // no need to copy static structure
		processStates = new HashMap<>();
		for (Map.Entry<XCFA.Process, ProcessState> entry : toCopy.processStates.entrySet()) {
			processStates.put(entry.getKey(), new ProcessState(this, entry.getValue()));
		}
	}

	public Collection<Transition> getEnabledTransitions() {
		ArrayList<Transition> enabledTransitions = new ArrayList<>();
		for (Map.Entry<XCFA.Process, ProcessState> entry : processStates.entrySet()) {
			entry.getValue().collectEnabledTransitions(this, enabledTransitions);
		}
		return enabledTransitions;
	}

	public boolean step(Scheduler sched) {
		Collection<Transition> enabledTransitions = getEnabledTransitions();
		if (enabledTransitions.isEmpty())
			return false;
		sched.getNextTransition(enabledTransitions).step(this);
		return true;
	}


}
