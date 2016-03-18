package hu.bme.mit.inf.ttmc.cegar.common.steps;

import hu.bme.mit.inf.ttmc.cegar.common.data.AbstractResult;
import hu.bme.mit.inf.ttmc.cegar.common.data.IAbstractState;
import hu.bme.mit.inf.ttmc.cegar.common.data.IAbstractSystem;

/**
 * Common interface for model checking.
 * @author Akos
 * @param <AbstractSystemType> Type of the abstract system
 * @param <AbstractStateType> Type of the abstract states
 */
public interface IChecker<AbstractSystemType extends IAbstractSystem, AbstractStateType extends IAbstractState> {
	/**
	 * Check whether the abstract system meets the specification
	 * @param system System
	 * @return Result of the model checking, which is either a counterexample or an inductive invariant
	 */
	AbstractResult<AbstractStateType> check(AbstractSystemType system);
}
