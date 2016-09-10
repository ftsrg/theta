package hu.bme.mit.theta.splittingcegar.interpolating.steps.refinement;

import java.util.List;

import hu.bme.mit.theta.splittingcegar.interpolating.data.Interpolant;
import hu.bme.mit.theta.splittingcegar.interpolating.data.InterpolatedAbstractState;
import hu.bme.mit.theta.splittingcegar.interpolating.data.InterpolatedAbstractSystem;

public interface Splitter {
	public int split(InterpolatedAbstractSystem system, List<InterpolatedAbstractState> abstractCounterEx, Interpolant interpolant);
}
