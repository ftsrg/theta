package hu.bme.mit.inf.ttmc.cegar.common.steps;

import java.util.List;

import hu.bme.mit.inf.ttmc.cegar.common.data.ConcreteTrace;
import hu.bme.mit.inf.ttmc.cegar.common.data.IAbstractState;
import hu.bme.mit.inf.ttmc.cegar.common.data.IAbstractSystem;

/**
 * Common interface for abstraction refinement.
 * 
 * @author Akos
 * @param <AbstractSystemType>
 *            Type of the abstract system
 * @param <AbstractStateType>
 *            Type of the abstract states
 */
public interface IRefiner<AbstractSystemType extends IAbstractSystem, AbstractStateType extends IAbstractState> extends IStoppable {
	/**
	 * Refine the abstraction based on the abstract counterexample and the
	 * concrete trace
	 * 
	 * @param system
	 *            System
	 * @param abstractCounterEx
	 *            Abstract counterexample
	 * @param concreteTrace
	 *            Concrete trace
	 * @return Refined abstract system
	 */
	AbstractSystemType refine(AbstractSystemType system, List<AbstractStateType> abstractCounterEx, ConcreteTrace concreteTrace);
}
