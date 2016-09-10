package hu.bme.mit.theta.splittingcegar.common.steps;

import hu.bme.mit.theta.splittingcegar.common.data.AbstractResult;
import hu.bme.mit.theta.splittingcegar.common.data.AbstractState;
import hu.bme.mit.theta.splittingcegar.common.data.AbstractSystem;

/**
 * Common interface for model checking.
 */
public interface Checker<AbstractSystemType extends AbstractSystem, AbstractStateType extends AbstractState> {
	AbstractResult<AbstractStateType> check(AbstractSystemType system);
}
