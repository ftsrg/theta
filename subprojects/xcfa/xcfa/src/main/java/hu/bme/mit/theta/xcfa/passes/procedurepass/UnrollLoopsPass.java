package hu.bme.mit.theta.xcfa.passes.procedurepass;
import hu.bme.mit.theta.xcfa.model.XcfaProcedure;

/**
 * This pass unrolls an XCFA Procedure exactly once per loop. By re-running this pass on an otherwise unmodified
 * XCFA Procedure, it will unroll it once more. Any modification might cause exponential expansion of the loops and is
 * therefore unlikely to function well.
 * The unrolling algorithm is the following:
 * 		0a. Collect all initially existing locations and edges (skip this step in the first iteration, everything is in this set)
 * 		0b. Collect all locations and edges added in the last iteration (skip this step in the first iteration, everything is in this set)
 * 		1. Add a copy of 0a to the procedure builder
 * 		2. For every reverse-edge in the 0b set add an edge from 0b to the corresponding new location (old_source -> new_target)
 * 		3. For every (all previous) reverse-edge-source location add an edge from each incoming edge's corresponding new location (new_source -> old_targets )
 */
public class UnrollLoopsPass extends ProcedurePass{
	private static final int K = 1;

	@Override
	public XcfaProcedure.Builder run(XcfaProcedure.Builder builder) {

		return builder;
	}

}
