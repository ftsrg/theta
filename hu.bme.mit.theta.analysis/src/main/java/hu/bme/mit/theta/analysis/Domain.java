package hu.bme.mit.theta.analysis;

/**
 * Common interface for abstract domain with top and bottom elements and a
 * partial order.
 */
public interface Domain<S extends State> {

	/**
	 * Checks if the given state is a top element in the domain.
	 *
	 * @param state
	 * @return
	 */
	boolean isTop(S state);

	/**
	 * Checks if the given state is a bottom element in the domain.
	 *
	 * @param state
	 * @return
	 */
	boolean isBottom(S state);

	/**
	 * Checks if state1 is less or equal to state2.
	 *
	 * @param state1
	 * @param state2
	 * @return
	 */
	boolean isLeq(S state1, S state2);

}
