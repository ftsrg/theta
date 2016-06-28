package hu.bme.mit.inf.ttmc.cegar.common.steps;

import java.util.List;

import hu.bme.mit.inf.ttmc.cegar.common.data.AbstractState;
import hu.bme.mit.inf.ttmc.cegar.common.data.AbstractSystem;
import hu.bme.mit.inf.ttmc.cegar.common.data.ConcreteTrace;

/**
 * Common interface for concretizing abstract counterexamples.
 */
public interface Concretizer<AbstractSystemType extends AbstractSystem, AbstractStateType extends AbstractState> {
	ConcreteTrace concretize(AbstractSystemType system, List<AbstractStateType> abstractCounterex);
}
