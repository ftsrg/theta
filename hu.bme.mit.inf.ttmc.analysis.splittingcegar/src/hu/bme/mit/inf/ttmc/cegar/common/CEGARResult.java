package hu.bme.mit.inf.ttmc.cegar.common;

import static com.google.common.base.Preconditions.checkArgument;

import java.util.Collection;
import java.util.Map;

import hu.bme.mit.inf.ttmc.cegar.common.data.ConcreteTrace;
import hu.bme.mit.inf.ttmc.cegar.common.data.IAbstractState;
import hu.bme.mit.inf.ttmc.cegar.common.data.IAbstractSystem;
import hu.bme.mit.inf.ttmc.formalism.sts.STS;

/**
 * Represents the result of the CEGAR algorithm containing the counterexample
 * (if found) and run-time data.
 *
 * @author Akos
 */
public class CEGARResult {
	private final STS system;
	private final boolean specificationHolds; // Does the specification hold
	private final ConcreteTrace counterExample; // Concrete counterexample (if found)
	private final Collection<? extends IAbstractState> exploredStates; // Inductive invariant (if the property holds)
	private final long elapsedMillis; // Elapsed time
	private final int refinementCount; // Number of refinements
	private final Map<String, Long> detailedTime; // Details of the elapsed time
	private final int stateSpaceSize; // Size of the explored state space
	private final IAbstractSystem absSys;

	/**
	 * Initialize result (specification does not hold)
	 *
	 * @param counterExample
	 *            Concrete counterexample, must not be null
	 * @param elapsedMillis
	 *            Elapsed time
	 * @param refinementCount
	 *            Number of refinements
	 * @param detailedTime
	 *            Details of the elapsed time
	 */
	public CEGARResult(final STS system, final ConcreteTrace counterExample, final long elapsedMillis, final int refinementCount,
			final Map<String, Long> detailedTime, final int stateSpaceSize, final IAbstractSystem absSys) {
		checkArgument(counterExample != null);

		this.system = system;
		this.counterExample = counterExample;
		this.exploredStates = null;
		this.elapsedMillis = elapsedMillis;
		this.refinementCount = refinementCount;
		this.specificationHolds = (counterExample == null);
		this.detailedTime = detailedTime;
		this.stateSpaceSize = stateSpaceSize;
		this.absSys = absSys;
	}

	/**
	 * Initialize result (specification holds)
	 *
	 * @param inductiveInvariant
	 *            Inductive invariant, must not be null
	 * @param elapsedMillis
	 *            Elapsed time
	 * @param refinementCount
	 *            Number of refinements
	 * @param detailedTime
	 *            Details of the elapsed time
	 */
	public CEGARResult(final STS system, final Collection<? extends IAbstractState> exploredStates, final long elapsedMillis, final int refinementCount,
			final Map<String, Long> detailedTime, final int stateSpaceSize, final IAbstractSystem absSys) {
		checkArgument(exploredStates != null); // TODO: implement inductive inv.

		this.system = system;
		this.counterExample = null;
		this.exploredStates = exploredStates;
		this.elapsedMillis = elapsedMillis;
		this.refinementCount = refinementCount;
		this.specificationHolds = (counterExample == null);
		this.detailedTime = detailedTime;
		this.stateSpaceSize = stateSpaceSize;
		this.absSys = absSys;
	}

	/**
	 * Get whether the specification holds
	 *
	 * @return True if the specification holds, false otherwise
	 */
	public boolean specificationHolds() {
		return specificationHolds;
	}

	/**
	 * Get the concrete counterexample
	 *
	 * @return Concrete counterexample if the specification does not hold, null
	 *         otherwise
	 */
	public ConcreteTrace getCounterExample() {
		return counterExample;
	}

	/**
	 * Get the inductive invariant
	 *
	 * @return Inductive invariant if the specification holds, null otherwise
	 */
	public Collection<? extends IAbstractState> getExploredStates() {
		return exploredStates;
	}

	public STS getSystem() {
		return system;
	}

	/**
	 * Get the elapsed time in milliseconds
	 *
	 * @return Elapsed time in milliseconds
	 */
	public long getElapsedMillis() {
		return elapsedMillis;
	}

	/**
	 * Get the number of refinements
	 *
	 * @return Number of refinements
	 */
	public int getRefinementCount() {
		return refinementCount;
	}

	/**
	 * Get the details of the elapsed time
	 *
	 * @return Details of the elapsed time
	 */
	public Map<String, Long> getDetailedTime() {
		return detailedTime;
	}

	/**
	 * Get the size of the explored state space
	 *
	 * @return Size of the explored state space
	 */
	public int getStateSpaceSize() {
		return stateSpaceSize;
	}

	public IAbstractSystem getAbstractSystem() {
		return absSys;
	}
}
