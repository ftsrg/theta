package hu.bme.mit.inf.ttmc.cegar.interpolatingcegar.steps.refinement;

import hu.bme.mit.inf.ttmc.cegar.common.data.ConcreteTrace;
import hu.bme.mit.inf.ttmc.cegar.interpolatingcegar.data.Interpolant;
import hu.bme.mit.inf.ttmc.cegar.interpolatingcegar.data.InterpolatedAbstractState;
import hu.bme.mit.inf.ttmc.cegar.interpolatingcegar.data.InterpolatedAbstractSystem;

import java.util.List;

/**
 * Common interface for interpolaters.
 * @author Akos
 */
public interface IInterpolater {
	/**
	 * Calculate interpolant
	 * @param system System
	 * @param abstractCounterEx Abstract counterexample
	 * @param concreteTrace Concrete trace corresponding to the longest prefix of the abstract counterexample
	 * @return Interpolant
	 */
	public Interpolant interpolate(InterpolatedAbstractSystem system,
			List<InterpolatedAbstractState> abstractCounterEx, ConcreteTrace concreteTrace);
}
