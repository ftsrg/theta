package hu.bme.mit.theta.xcfa.simulator;

/**
 * A transition is the atomic unit of execution.
 *
 * This interface is used to update the state.
 *
 * Mostly corresponds to one statement. (Exception: LeaveTransition)
 *
 * A transition instance should be independent of ExplStates.
 * Thus, a transition could be cached later.
 *
 * 	   For this, a procedure wrapper was created (ProcedureData)
 *
 * TODO decouple from ExplState? (use a State interface instead)
 */
public interface Transition {

	/**
	 * Updates the runtime state by the transition
	 * Should be called only by ExplState.
	 * @param state The ExplState to be updated
	 */
	void execute(ExplState state);

	/**
	 * Checks whether a transition is enabled.
	 * @param state The current state
	 * @return Returns whether this transition is enabled
	 */
	boolean enabled(ExplState state);
}
