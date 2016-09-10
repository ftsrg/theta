package hu.bme.mit.theta.analysis.sts.pred;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;
import java.util.HashSet;
import java.util.Set;

import hu.bme.mit.theta.analysis.InitFunction;
import hu.bme.mit.theta.analysis.pred.PredPrecision;
import hu.bme.mit.theta.analysis.pred.PredState;
import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.expr.impl.Exprs;
import hu.bme.mit.theta.core.type.BoolType;
import hu.bme.mit.theta.formalism.common.Valuation;
import hu.bme.mit.theta.formalism.sts.STS;
import hu.bme.mit.theta.formalism.utils.PathUtils;
import hu.bme.mit.theta.solver.Solver;

class StsPredInitFunction implements InitFunction<PredState, PredPrecision> {

	private final Collection<Expr<? extends BoolType>> init;
	private final Collection<Expr<? extends BoolType>> invar;
	private final Solver solver;

	StsPredInitFunction(final STS sts, final Solver solver) {
		this.init = checkNotNull(sts.getInit());
		this.invar = checkNotNull(sts.getInvar());
		this.solver = checkNotNull(solver);
	}

	@Override
	public Collection<PredState> getInitStates(final PredPrecision precision) {
		checkNotNull(precision);

		final Set<PredState> initStates = new HashSet<>();
		boolean moreInitStates;
		solver.push();
		// TODO: optimization: cache the unrolled init and invar for 0
		init.stream().forEach(i -> solver.add(PathUtils.unfold(i, 0)));
		invar.stream().forEach(i -> solver.add(PathUtils.unfold(i, 0)));
		do {
			moreInitStates = solver.check().boolValue();
			if (moreInitStates) {
				final Valuation nextInitStateVal = PathUtils.extractValuation(solver.getModel(), 0);

				final PredState nextInitState = precision.mapToAbstractState(nextInitStateVal);
				initStates.add(nextInitState);
				solver.add(PathUtils.unfold(Exprs.Not(nextInitState.toExpr()), 0));
			}
		} while (moreInitStates);
		solver.pop();

		return initStates;
	}

}
