package hu.bme.mit.inf.ttmc.cegar.common.steps;

import hu.bme.mit.inf.ttmc.cegar.common.data.AbstractResult;
import hu.bme.mit.inf.ttmc.cegar.common.data.AbstractState;
import hu.bme.mit.inf.ttmc.cegar.common.data.AbstractSystem;

/**
 * Common interface for model checking.
 */
public interface Checker<AbstractSystemType extends AbstractSystem, AbstractStateType extends AbstractState> extends Stoppable {
	AbstractResult<AbstractStateType> check(AbstractSystemType system);
}
