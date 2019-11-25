package hu.bme.mit.theta.xcfa.simulator;

/**
 * A transition instance should be independent of a RuntimeState.
 * This is used to progress a state.
 * TODO cache these transitions (the same line can get the same instance of transition)
 * 	   For this, a procedure wrapper could be created (which could cache every static data in CallState)
 */
public interface Transition {
	void step(RuntimeState state) throws ErrorReachedException;

	boolean enabled(RuntimeState state);
}
