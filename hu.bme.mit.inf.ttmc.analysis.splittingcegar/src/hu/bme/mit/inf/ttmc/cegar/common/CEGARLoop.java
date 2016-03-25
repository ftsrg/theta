package hu.bme.mit.inf.ttmc.cegar.common;

import hu.bme.mit.inf.ttmc.cegar.common.steps.Stoppable;
import hu.bme.mit.inf.ttmc.formalism.sts.STS;

/**
 * Common interface for CEGAR algorithms.
 */
public interface CEGARLoop extends Stoppable {

	public CEGARResult check(STS concreteSys);

}
