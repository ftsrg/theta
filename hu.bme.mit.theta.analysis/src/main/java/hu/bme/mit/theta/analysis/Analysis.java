package hu.bme.mit.theta.analysis;

/**
 * Common interface for analyses, containing a domain, an initial and a transfer
 * function.
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
	InitFunction<S, P> getInitFunction();

	/**
	 * Gets the transfer function.
	 *
	 * @return
	 */
	TransferFunction<S, A, P> getTransferFunction();

}
