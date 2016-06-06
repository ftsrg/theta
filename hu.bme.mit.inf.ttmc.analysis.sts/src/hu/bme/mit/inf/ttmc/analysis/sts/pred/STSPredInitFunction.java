package hu.bme.mit.inf.ttmc.analysis.sts.pred;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;
import java.util.HashSet;
import java.util.Set;

import hu.bme.mit.inf.ttmc.analysis.InitFunction;
import hu.bme.mit.inf.ttmc.analysis.pred.PredPrecision;
import hu.bme.mit.inf.ttmc.analysis.pred.PredState;
import hu.bme.mit.inf.ttmc.core.expr.Expr;
import hu.bme.mit.inf.ttmc.core.expr.impl.Exprs;
import hu.bme.mit.inf.ttmc.core.type.BoolType;
import hu.bme.mit.inf.ttmc.formalism.common.Valuation;
import hu.bme.mit.inf.ttmc.formalism.utils.PathUtils;
import hu.bme.mit.inf.ttmc.solver.Solver;

public class STSPredInitFunction implements InitFunction<PredState, PredPrecision, Expr<? extends BoolType>> {

	private final Solver solver;

	STSPredInitFunction(final Solver solver) {
		this.solver = solver;
	}

	@Override
	public Collection<PredState> getInitStates(final PredPrecision precision, final Expr<? extends BoolType> init) {
		checkNotNull(precision);
		final Set<PredState> initStates = new HashSet<>();
		boolean moreInitStates;
		solver.push();
		solver.add(PathUtils.unfold(init, 0));
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
