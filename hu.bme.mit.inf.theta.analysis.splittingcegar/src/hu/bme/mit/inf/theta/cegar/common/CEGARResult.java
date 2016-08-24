package hu.bme.mit.inf.theta.cegar.common;

import static com.google.common.base.Preconditions.checkArgument;

import java.util.Collection;
import java.util.Map;

import hu.bme.mit.inf.theta.cegar.common.data.AbstractState;
import hu.bme.mit.inf.theta.cegar.common.data.AbstractSystem;
import hu.bme.mit.inf.theta.cegar.common.data.ConcreteTrace;
import hu.bme.mit.inf.theta.formalism.sts.STS;

/**
 * Represents the result of the CEGAR algorithm containing the counterexample
 * (if found) and run-time data.
 */
public class CEGARResult {
	private final AbstractSystem absSys;
	private final boolean propertyHolds;
	private final ConcreteTrace counterExample;
	private final Collection<? extends AbstractState> exploredStates;
	private final long elapsedMillis;
	private final int refinementCount;
	private final Map<String, Long> detailedTime;
	private final int stateSpaceSize;

	/**
	 * Initialize result (specification does not hold)
	 */
	public CEGARResult(final STS system, final ConcreteTrace counterExample, final long elapsedMillis, final int refinementCount,
			final Map<String, Long> detailedTime, final int stateSpaceSize, final AbstractSystem absSys) {
		checkArgument(counterExample != null);
		this.counterExample = counterExample;
		this.exploredStates = null;
		this.elapsedMillis = elapsedMillis;
		this.refinementCount = refinementCount;
		this.propertyHolds = (counterExample == null);
		this.detailedTime = detailedTime;
		this.stateSpaceSize = stateSpaceSize;
		this.absSys = absSys;
	}

	/**
	 * Initialize result (specification holds)
	 */
	public CEGARResult(final STS system, final Collection<? extends AbstractState> exploredStates, final long elapsedMillis, final int refinementCount,
			final Map<String, Long> detailedTime, final int stateSpaceSize, final AbstractSystem absSys) {
		checkArgument(exploredStates != null);
		this.counterExample = null;
		this.exploredStates = exploredStates;
		this.elapsedMillis = elapsedMillis;
		this.refinementCount = refinementCount;
		this.propertyHolds = (counterExample == null);
		this.detailedTime = detailedTime;
		this.stateSpaceSize = stateSpaceSize;
		this.absSys = absSys;
	}

	public boolean propertyHolds() {
		return propertyHolds;
	}

	public ConcreteTrace getCounterExample() {
		return counterExample;
	}

	public Collection<? extends AbstractState> getExploredStates() {
		return exploredStates;
	}

	public STS getSTS() {
		return absSys.getSTS();
	}

	public long getElapsedMillis() {
		return elapsedMillis;
	}

	public int getRefinementCount() {
		return refinementCount;
	}

	public Map<String, Long> getDetailedTime() {
		return detailedTime;
	}

	public int getStateSpaceSize() {
		return stateSpaceSize;
	}

	public AbstractSystem getAbstractSystem() {
		return absSys;
	}
}
