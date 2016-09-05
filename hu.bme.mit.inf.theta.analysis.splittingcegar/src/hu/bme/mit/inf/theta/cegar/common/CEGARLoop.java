package hu.bme.mit.inf.theta.cegar.common;

import hu.bme.mit.inf.theta.formalism.sts.STS;

/**
 * Common interface for CEGAR algorithms.
 */
public interface CEGARLoop {

	public CEGARResult check(STS concreteSys);

	public void stop();

}
