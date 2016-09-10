package hu.bme.mit.theta.splittingcegar.common.steps;

import java.util.List;

import hu.bme.mit.theta.splittingcegar.common.data.AbstractState;
import hu.bme.mit.theta.splittingcegar.common.data.AbstractSystem;
import hu.bme.mit.theta.splittingcegar.common.data.ConcreteTrace;

/**
 * Common interface for abstraction refinement.
 */
public interface Refiner<AbstractSystemType extends AbstractSystem, AbstractStateType extends AbstractState> {
	AbstractSystemType refine(AbstractSystemType system, List<AbstractStateType> abstractCounterEx, ConcreteTrace concreteTrace);
}
