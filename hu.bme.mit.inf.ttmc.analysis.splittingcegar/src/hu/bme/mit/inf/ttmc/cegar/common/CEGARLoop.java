package hu.bme.mit.inf.ttmc.cegar.common;

import hu.bme.mit.inf.ttmc.formalism.sts.STS;

/**
 * Common interface for CEGAR algorithms.
 */
public interface CEGARLoop {

	public CEGARResult check(STS concreteSys);

	public void stop();

}
