package hu.bme.mit.theta.analysis;

/**
 * Common interface for analyses.
 *
 * @see Domain
 * @see InitFunc
 * @see TransferFunc
 */
public interface Analysis<S extends State, A extends Action, P extends Prec> {

	/**
	 * Gets the domain.
	 *
	 * @return
	 */
	Domain<S> getDomain();

	/**
	 * Gets the initial function.
	 *
	 * @return
	 */
	InitFunc<S, P> getInitFunc();

	/**
	 * Gets the transfer function.
	 *
	 * @return
	 */
	TransferFunc<S, A, P> getTransferFunc();

}
