package hu.bme.mit.inf.ttmc.slicer;

import java.util.List;
import java.util.function.Predicate;

import hu.bme.mit.inf.ttmc.slicer.cfg.CFG;
import hu.bme.mit.inf.ttmc.slicer.cfg.CFGNode;

public interface CFGSlicer {

	/**
	 * Return all slices on nodes satisfying a given predicate
	 *
	 * @param input The CFG to be sliced
	 * @param pred A predicate which will determine the criteria
	 *
	 * @return A list of CFGs representing the slices
	 */
	public List<CFG> allSlices(CFG input, Predicate<CFGNode> pred);

	/**
	 * Slice a CFG by a single criteria node
	 *
	 * @param input The CFG to be sliced
	 * @param criteria The criteria to be sliced on
	 *
	 * @return A list of CFGs representing the slices
	 */
	public CFG slice(CFG input, CFGNode criteria);

}
