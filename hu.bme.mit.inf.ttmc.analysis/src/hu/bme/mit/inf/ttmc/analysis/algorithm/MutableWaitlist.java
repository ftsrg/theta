package hu.bme.mit.inf.ttmc.analysis.algorithm;

import hu.bme.mit.inf.ttmc.analysis.State;

public interface MutableWaitlist<S extends State<S>> extends Waitlist<S> {

	public S pop();

}
