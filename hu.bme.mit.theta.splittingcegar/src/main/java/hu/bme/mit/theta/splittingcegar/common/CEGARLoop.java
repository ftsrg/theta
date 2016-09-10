package hu.bme.mit.theta.splittingcegar.common;

import hu.bme.mit.theta.formalism.sts.STS;

/**
 * Common interface for CEGAR algorithms.
 */
public interface CEGARLoop {

	public CEGARResult check(STS concreteSys);

	public void stop();

}
