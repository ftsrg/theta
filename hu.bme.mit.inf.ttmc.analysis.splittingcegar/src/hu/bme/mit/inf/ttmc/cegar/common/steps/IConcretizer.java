package hu.bme.mit.inf.ttmc.cegar.common.steps;

import java.util.List;

import hu.bme.mit.inf.ttmc.cegar.common.data.ConcreteTrace;
import hu.bme.mit.inf.ttmc.cegar.common.data.IAbstractState;
import hu.bme.mit.inf.ttmc.cegar.common.data.IAbstractSystem;

/**
 * Common interface for concretizing abstract counterexamples.
 * 
 * @author Akos
 * @param <AbstractSystemType>
 *            Type of the abstract system
 * @param <AbstractStateType>
 *            Type of the abstract states
 */
public interface IConcretizer<AbstractSystemType extends IAbstractSystem, AbstractStateType extends IAbstractState> extends IStoppable {
	/**
	 * Get the longest concrete trace corresponding to an abstract
	 * counterexample
	 * 
	 * @param system
	 *            System
	 * @param abstractCounterex
	 *            Abstract counterexample
	 * @return Concrete trace
	 */
	ConcreteTrace concretize(AbstractSystemType system, List<AbstractStateType> abstractCounterex);
}
