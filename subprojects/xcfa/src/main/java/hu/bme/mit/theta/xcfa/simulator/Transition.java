package hu.bme.mit.theta.xcfa.simulator;

/**
 * A transition is a unit of execution.
 * Mostly corresponds to a statement, but this is not guaranteed in the future
 * A transition instance should be independent of a RuntimeState.
 * This is used to progress a state.
 * TODO cache these transitions (the same line can get the same instance of transition)
 * 	   For this, a procedure wrapper could be created (which could cache every static data in CallState)
 *
 * In the future, transition should probably be the smallest unit which can be done atomically
 *   This would solve the AtomicBegin/AtomicEnd pair.
 *   For example, a list of atomic operations could be a transition (a composite transition)
 */
public interface Transition {
	/**
	 * Updates the runtime state by the transition
	 * Should be called only by RuntimeState
	 * @param state The RuntimeState to be updated
	 * @throws ErrorReachedException Throws an error if the error location is reached or a deadlock is caught
	 */
	void step(RuntimeState state) throws ErrorReachedException;

	/**
	 * Checks whether a transition is enabled.
	 * @param state The current state
	 * @return Returns whether this transition is enabled
	 */
	boolean enabled(RuntimeState state);
}
