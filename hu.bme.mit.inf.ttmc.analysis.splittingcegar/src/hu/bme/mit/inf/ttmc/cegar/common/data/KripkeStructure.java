package hu.bme.mit.inf.ttmc.cegar.common.data;

import java.util.ArrayList;
import java.util.List;

/**
 * Represents a Kripke structure with states of type T
 * @author Akos
 * @param <T> Type of the states
 */
public class KripkeStructure<T> {
	private List<T> states; // States
	private List<T> initialStates; // Initial states
	
	/**
	 * Constructor
	 */
	public KripkeStructure() {
		states = new ArrayList<T>();
		initialStates = new ArrayList<T>();
	}

	/**
	 * Get the list of states
	 * @return List of states
	 */
	public List<T> getStates() {
		return states;
	}
	
	/**
	 * Get the ith state
	 * @param i Index
	 * @return ith state
	 */
	public T getState(int i){
		return states.get(i);
	}

	/**
	 * Get the list of initial states
	 * @return List of initial states
	 */
	public List<T> getInitialStates() {
		return initialStates;
	}
	
	/**
	 * Get the ith initial state
	 * @param i Index
	 * @return ith initial state
	 */
	public T getInitialState(int i){
		return initialStates.get(i);
	}
	
	/**
	 * Add a state
	 * @param state State to be added
	 */
	public void addState(T state){
		states.add(state);
	}
	
	/**
	 * Add an initial state
	 * @param state State to be added as initial
	 */
	public void addInitialState(T state){
		initialStates.add(state);
	}
	
}
