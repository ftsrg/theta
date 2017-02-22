package hu.bme.mit.theta.analysis.algorithm.cegar;

import java.util.Set;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.Trace;
import hu.bme.mit.theta.analysis.expl.ExplPrecision;
import hu.bme.mit.theta.analysis.expr.IndexedVarsRefutation;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.Type;

public class ExplVarsRefiner<S extends State, A extends Action>
		implements PrecRefiner<S, A, ExplPrecision, IndexedVarsRefutation> {

	@Override
	public ExplPrecision refine(final Trace<S, A> trace, final ExplPrecision precision,
			final IndexedVarsRefutation refutation) {
		final Set<VarDecl<? extends Type>> vars = refutation.getVarSets().getAllVars();
		final ExplPrecision refinedPrecision = precision.join(ExplPrecision.create(vars));
		return refinedPrecision;
	}

}
