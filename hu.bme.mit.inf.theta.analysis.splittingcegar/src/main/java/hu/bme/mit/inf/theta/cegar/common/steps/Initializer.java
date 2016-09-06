package hu.bme.mit.inf.theta.cegar.common.steps;

import hu.bme.mit.inf.theta.cegar.common.data.AbstractSystem;
import hu.bme.mit.inf.theta.formalism.sts.STS;

/**
 * Common interface for creating the initial abstract system.
 */
public interface Initializer<AbstractSystemType extends AbstractSystem> {
	AbstractSystemType create(STS sts);
}
