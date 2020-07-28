package hu.bme.mit.theta.xcfa.simulator;

import hu.bme.mit.theta.xcfa.XCFA;

/**
 * This is used for every transition within only one process.
 * Exception will (probably) be Wait/Notify/NotifyAll.
 */
abstract public class ProcessTransition implements Transition {

	protected final XCFA.Process process;

	public ProcessTransition(XCFA.Process p) {
		process = p;
	}

}
