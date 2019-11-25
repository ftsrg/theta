package hu.bme.mit.theta.xcfa.simulator;

import hu.bme.mit.theta.xcfa.XCFA;

abstract public class ProcessTransition implements Transition {

	protected XCFA.Process process;

	public ProcessTransition(XCFA.Process p) {
		process = p;
	}

}
