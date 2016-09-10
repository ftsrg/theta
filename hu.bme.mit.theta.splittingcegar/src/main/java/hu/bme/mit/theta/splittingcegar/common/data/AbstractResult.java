package hu.bme.mit.theta.splittingcegar.common.data;

import static com.google.common.base.Preconditions.checkArgument;

import java.util.Collection;
import java.util.List;
import java.util.Optional;

/**
 * Class that represents the result of model checking the abstract system. The
 * result is either a counterexample (property does not hold) or an inductive
 * invariant (property holds).
 */
public class AbstractResult<AbstractStateType> {
	private final Optional<List<AbstractStateType>> counterexample;
	private final Optional<Collection<? extends AbstractState>> exploredStates;
	private final int stateSpaceSize;

	public AbstractResult(final List<AbstractStateType> counterexample, final Collection<? extends AbstractState> exploredStates, final int stateSpaceSize) {
		checkArgument((counterexample == null && exploredStates != null) || counterexample != null && exploredStates == null);
		this.counterexample = Optional.ofNullable(counterexample);
		this.exploredStates = Optional.ofNullable(exploredStates);
		this.stateSpaceSize = stateSpaceSize;
	}

	public boolean isCounterExample() {
		return counterexample.isPresent();
	}

	public List<AbstractStateType> getCounterexample() {
		if (!isCounterExample())
			throw new RuntimeException("Cannot give counterexample since the property holds.");
		return counterexample.get();
	}

	public Collection<? extends AbstractState> getExploredStates() {
		if (isCounterExample())
			throw new RuntimeException("Cannot get inductive invariant since the property does not hold.");

		return exploredStates.get();
	}

	public int getStateSpaceSize() {
		return stateSpaceSize;
	}
}
