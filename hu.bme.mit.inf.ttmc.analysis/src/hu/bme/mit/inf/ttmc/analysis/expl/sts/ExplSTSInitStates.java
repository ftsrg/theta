package hu.bme.mit.inf.ttmc.analysis.expl.sts;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;
import java.util.HashSet;
import java.util.Set;

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
		checkNotNull(precision);
		final Set<ExplState> initStates = new HashSet<>();
		boolean moreInitStates;
		solver.push();
		solver.add(sts.unrollInit(0));
		solver.add(sts.unrollInv(0));
		do {
			moreInitStates = solver.check().boolValue();
			if (moreInitStates) {
				final Valuation nextInitStateVal = sts.getConcreteState(solver.getModel(), 0);
				final ExplState nextInitState = precision.createState(nextInitStateVal);
				initStates.add(nextInitState);
				solver.add(sts.unroll(Exprs.Not(nextInitState.asExpr()), 0));
			}
		} while (moreInitStates);
		solver.pop();
		return initStates;
	}

}
