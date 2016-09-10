package hu.bme.mit.theta.splittingcegar.common.utils.debugging;

import java.util.List;

import hu.bme.mit.theta.splittingcegar.common.data.AbstractState;
import hu.bme.mit.theta.splittingcegar.common.data.AbstractSystem;
import hu.bme.mit.theta.splittingcegar.common.data.ConcreteTrace;

/**
 * Common interface for debugging. Each function returns a reference to the
 * current debugger instance, thus functions can be chained:
 * debugger.explore(...).setAbstractCE(...).visualize().
 */
public interface Debugger<AbstractSystemType extends AbstractSystem, AbstractStateType extends AbstractState> {

	Debugger<AbstractSystemType, AbstractStateType> explore(AbstractSystemType system);

	Debugger<AbstractSystemType, AbstractStateType> clearStateSpace();

	Debugger<AbstractSystemType, AbstractStateType> setAbstractCE(List<AbstractStateType> ace);

	Debugger<AbstractSystemType, AbstractStateType> clearAbstractCE();

	Debugger<AbstractSystemType, AbstractStateType> setConcreteTrace(ConcreteTrace cce);

	Debugger<AbstractSystemType, AbstractStateType> clearConcreteTrace();

	Debugger<AbstractSystemType, AbstractStateType> visualize();
}
