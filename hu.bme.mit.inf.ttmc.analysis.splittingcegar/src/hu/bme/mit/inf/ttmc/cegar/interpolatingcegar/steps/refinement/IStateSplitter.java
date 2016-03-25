package hu.bme.mit.inf.ttmc.cegar.interpolatingcegar.steps.refinement;

import java.util.List;

import hu.bme.mit.inf.ttmc.cegar.common.steps.Stoppable;
import hu.bme.mit.inf.ttmc.cegar.interpolatingcegar.data.Interpolant;
import hu.bme.mit.inf.ttmc.cegar.interpolatingcegar.data.InterpolatedAbstractState;
import hu.bme.mit.inf.ttmc.cegar.interpolatingcegar.data.InterpolatedAbstractSystem;

/**
 * Common interface for the state space splitters.
 * 
 * @author Akos
 */
public interface IStateSplitter extends Stoppable {
	/**
	 * Split abstract state(s) using the interpolant
	 * 
	 * @param system
	 *            System
	 * @param abstractCounterEx
	 *            Abstract counterexample
	 * @param interpolant
	 *            Interpolant
	 * @return Index of the first state in the abstract counterexample that was
	 *         split
	 */
	public int split(InterpolatedAbstractSystem system, List<InterpolatedAbstractState> abstractCounterEx, Interpolant interpolant);
}
