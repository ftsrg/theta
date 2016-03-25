package hu.bme.mit.inf.ttmc.cegar.common;

import hu.bme.mit.inf.ttmc.cegar.common.steps.Stoppable;
import hu.bme.mit.inf.ttmc.formalism.sts.STS;

/**
 * Common interface for different CEGAR algorithms.
 *
 * @author Akos
 */
public interface ICEGARLoop extends Stoppable {

	/**
	 * Check whether a system satisfies the specification. The algorithms may
	 * modify (e.g. transform) the system.
	 *
	 * @param concreteSystem
	 */
	public CEGARResult check(STS concreteSystem);

}
