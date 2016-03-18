package hu.bme.mit.inf.ttmc.cegar.common.utils.debugging;

import hu.bme.mit.inf.ttmc.cegar.common.data.ConcreteTrace;
import hu.bme.mit.inf.ttmc.cegar.common.data.IAbstractState;
import hu.bme.mit.inf.ttmc.cegar.common.data.IAbstractSystem;

import java.util.List;

/**
 * Common interface for debugging.
 * Each function returns a reference to the current debugger instance, thus
 * functions can be chained: debugger.explore(...).setAbstractCE(...).visualize().
 * @author Akos
 * @param <AbstractSystemType> Type of the abstract system
 * @param <AbstractStateType> Type of the abstract states
 */
public interface IDebugger<AbstractSystemType extends IAbstractSystem, AbstractStateType extends IAbstractState> {
	/**
	 * Explore the concrete state space of the system and if required, the abstract as well
	 * @param system System
	 * @return A reference to the current debugger instance
	 */
	IDebugger<AbstractSystemType, AbstractStateType> explore(AbstractSystemType system);

	/**
	 * Clear the explored state space in the debugger
	 * @return A reference to the current debugger instance
	 */
	IDebugger<AbstractSystemType, AbstractStateType> clearStateSpace();

	/**
	 * Mark the states of the abstract counterexample
	 * @param ace Abstract counterexample
	 * @return A reference to the current debugger instance
	 */
	IDebugger<AbstractSystemType, AbstractStateType> setAbstractCE(List<AbstractStateType> ace);

	/**
	 * Unmark the states of the abstract counterexample
	 * @return A reference to the current debugger instance
	 */
	IDebugger<AbstractSystemType, AbstractStateType> clearAbstractCE();

	/**
	 * Mark the states of the concrete trace
	 * @param cce Concrete trace
	 * @return A reference to the current debugger instance
	 */
	IDebugger<AbstractSystemType, AbstractStateType> setConcreteTrace(ConcreteTrace cce);

	/**
	 * Unmark the states of the concrete trace
	 * @return A reference to the current debugger instance
	 */
	IDebugger<AbstractSystemType, AbstractStateType> clearConcreteTrace();

	/**
	 * Visualize the explored state space and also the abstract counterexample
	 * and concrete trace if marked
	 * @return A reference to the current debugger instance
	 */
	IDebugger<AbstractSystemType, AbstractStateType> visualize();
}
