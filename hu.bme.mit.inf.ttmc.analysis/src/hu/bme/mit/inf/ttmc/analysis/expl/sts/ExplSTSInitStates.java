package hu.bme.mit.inf.ttmc.analysis.expl.sts;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;
import java.util.HashSet;
import java.util.Set;

import hu.bme.mit.inf.ttmc.analysis.ExprState;
import hu.bme.mit.inf.ttmc.analysis.InitStates;
import hu.bme.mit.inf.ttmc.analysis.expl.ExplPrecision;
import hu.bme.mit.inf.ttmc.analysis.expl.ExplState;
import hu.bme.mit.inf.ttmc.core.expr.impl.Exprs;
import hu.bme.mit.inf.ttmc.formalism.common.Valuation;
import hu.bme.mit.inf.ttmc.formalism.sts.STS;
import hu.bme.mit.inf.ttmc.solver.Solver;

public class ExplSTSInitStates implements InitStates<ExplState, ExplPrecision> {

	private final Solver solver;
	private final STS sts;

	public ExplSTSInitStates(final STS sts, final Solver solver) {
		this.sts = checkNotNull(sts);
		this.solver = checkNotNull(solver);
	}

	@Override
	public Collection<? extends ExplState> get(final ExplPrecision precision) {
		final Set<ExplState> initStates = new HashSet<>();
		boolean moreInitialStates;

		do {
			Valuation nextInitStateVal = null;
			solver.push();
			solver.add(sts.unrollInit(0));
			solver.add(sts.unrollInv(0));
			for (final ExprState existingInit : initStates)
				solver.add(sts.unroll(Exprs.Not(existingInit.asExpr()), 0));

			moreInitialStates = solver.check().boolValue();
			if (moreInitialStates) {
				nextInitStateVal = sts.getConcreteState(solver.getModel(), 0, precision.getVisibleVars());
				initStates.add(ExplState.create(nextInitStateVal));
			}
			solver.pop();
		} while (moreInitialStates);

		return initStates;
	}

}
