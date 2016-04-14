package hu.bme.mit.inf.ttmc.cegar.common.steps;

import hu.bme.mit.inf.ttmc.cegar.common.data.AbstractSystem;
import hu.bme.mit.inf.ttmc.formalism.sts.STS;

/**
 * Common interface for creating the initial abstract system.
 */
public interface Initializer<AbstractSystemType extends AbstractSystem> {
	AbstractSystemType create(STS sts);
}
