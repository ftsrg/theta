package hu.bme.mit.theta.splittingcegar.common.steps;

import hu.bme.mit.theta.formalism.sts.STS;
import hu.bme.mit.theta.splittingcegar.common.data.AbstractSystem;

/**
 * Common interface for creating the initial abstract system.
 */
public interface Initializer<AbstractSystemType extends AbstractSystem> {
	AbstractSystemType create(STS sts);
}
