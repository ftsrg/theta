package hu.bme.mit.inf.ttmc.cegar.common.data;

import java.util.Collection;
import java.util.List;

/**
 * Class that represents the result of model checking the abstract system.
 * The result is either a counterexample (property does not hold) or an
 * inductive invariant (property holds).
 * @author Akos
 * @param <AbstractStateType> Type of the abstract states
 */
public class AbstractResult<AbstractStateType> {
	private List<AbstractStateType> counterexample; // Counterexample
	private Collection<? extends IAbstractState> exploredStates; // The inductive invariant is currently stored as the set of states internally
	private int stateSpaceSize; // Size of the explored states
	
	/**
	 * Constructor. Either a counterexample or the explored states must be given, i.e.,
	 * (counterexample==null) XOR (exploredStates==null) is assumed.
	 * @param counterexample Counterexample
	 * @param exploredStates Explored states
	 */
	public AbstractResult(List<AbstractStateType> counterexample,
			Collection<? extends IAbstractState> exploredStates, int stateSpaceSize) {
		this.counterexample = counterexample;
		this.exploredStates = exploredStates;
		this.stateSpaceSize = stateSpaceSize;
		
		if (this.counterexample == null && this.exploredStates == null)
			throw new RuntimeException("Counterexample and explored states cannot be both null");
		if (this.counterexample != null && this.exploredStates != null)
			throw new RuntimeException("Counterexample and explored states cannot be both not null");
			
	}
	
	/**
	 * Is the result a counterexample
	 * @return True if counterexample, false otherwise
	 */
	public boolean isCounterExample() {
		return counterexample != null;
	}
	
	/**
	 * Get the counterexample (if result is counterexample)
	 * @return Counterexample
	 */
	public List<AbstractStateType> getCounterexample() {
		if (counterexample == null) throw new RuntimeException("Cannot give counterexample since the property holds");
		return counterexample;
	}
	
	/**
	 * Get the inductive invariant (if result is an inductive invariant)
	 * @return Inductive invariant
	 */
	public Collection<? extends IAbstractState> getExploredStates() {
		if (exploredStates == null)
			throw new RuntimeException("Cannot get inductive invariant since a counterexample is given");

		return exploredStates;
	}
	
	/**
	 * Get the size of the explored state space
	 * @return Size of the explored state space
	 */
	public int getStateSpaceSize() {
		return stateSpaceSize;
	}
}
