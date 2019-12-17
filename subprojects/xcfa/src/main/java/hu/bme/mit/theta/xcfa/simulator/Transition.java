package hu.bme.mit.theta.xcfa.simulator;

/**
 * A transition is the atomic unit of execution.
 *
 * This interface is used to update the state.
 *
 * Mostly corresponds to one statement. (Exception: LeaveTransition, in the future: atomics)
 *
 * A transition instance should be independent of ExplStates.
 * Thus, a transition could be cached later.
 * TODO cache these transitions (the same line can get the same instance of transition)
 *
 * 	   For this, a procedure wrapper was created (ProcedureData)
 *
 * TODO create AtomicTransition
 *   This would solve the AtomicBegin/AtomicEnd pair.
 *   For example, a list of atomic operations could be a (composite) transition
 *
 */
public interface Transition {

	/**
	 * Updates the runtime state by the transition
	 * Should be called only by ExplState.
	 *
	 * // TODO rename to execute
	 * @param state The ExplState to be updated
	 */
	void step(ExplState state);

	/**
	 * Checks whether a transition is enabled.
	 * @param state The current state
	 * @return Returns whether this transition is enabled
	 */
	boolean enabled(ExplState state);
}
