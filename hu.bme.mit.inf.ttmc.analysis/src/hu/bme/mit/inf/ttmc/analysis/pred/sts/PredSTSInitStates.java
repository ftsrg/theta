package hu.bme.mit.inf.ttmc.analysis.pred.sts;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;
import java.util.HashSet;
import java.util.Set;

import hu.bme.mit.inf.ttmc.analysis.InitStates;
import hu.bme.mit.inf.ttmc.analysis.pred.PredPrecision;
import hu.bme.mit.inf.ttmc.analysis.pred.PredState;
import hu.bme.mit.inf.ttmc.core.expr.impl.Exprs;
import hu.bme.mit.inf.ttmc.formalism.common.Valuation;
import hu.bme.mit.inf.ttmc.formalism.sts.STS;
import hu.bme.mit.inf.ttmc.solver.Solver;

public class PredSTSInitStates implements InitStates<PredState, PredPrecision> {

	private final Solver solver;
	private final STS sts;

	public PredSTSInitStates(final STS sts, final Solver solver) {
		this.sts = checkNotNull(sts);
		this.solver = checkNotNull(solver);
	}

	@Override
	public Collection<? extends PredState> get(final PredPrecision precision) {
		checkNotNull(precision);
		final Set<PredState> initStates = new HashSet<>();
		boolean moreInitStates;
		solver.push();
		solver.add(sts.unrollInit(0));
		solver.add(sts.unrollInv(0));
		do {
			moreInitStates = solver.check().boolValue();
			if (moreInitStates) {
				final Valuation nextInitStateVal = sts.getConcreteState(solver.getModel(), 0);

				final PredState nextInitState = precision.mapToAbstractState(nextInitStateVal);
				initStates.add(nextInitState);
				solver.add(sts.unroll(Exprs.Not(nextInitState.asExpr()), 0));
			}
		} while (moreInitStates);
		solver.pop();

		return initStates;
	}

}
