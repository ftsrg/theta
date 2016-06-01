package hu.bme.mit.inf.ttmc.analysis.sts.expl;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;
import java.util.HashSet;
import java.util.Set;

import hu.bme.mit.inf.ttmc.analysis.InitFunction;
import hu.bme.mit.inf.ttmc.analysis.expl.ExplPrecision;
import hu.bme.mit.inf.ttmc.analysis.expl.ExplState;
import hu.bme.mit.inf.ttmc.core.expr.Expr;
import hu.bme.mit.inf.ttmc.core.expr.impl.Exprs;
import hu.bme.mit.inf.ttmc.core.type.BoolType;
import hu.bme.mit.inf.ttmc.formalism.common.Valuation;
import hu.bme.mit.inf.ttmc.formalism.utils.PathUtils;
import hu.bme.mit.inf.ttmc.solver.Solver;

class ExplInitFunction implements InitFunction<ExplState, ExplPrecision> {

	private final Solver solver;
	private final Expr<? extends BoolType> init;

	ExplInitFunction(final Solver solver, final Expr<? extends BoolType> init) {
		checkNotNull(solver);
		checkNotNull(init);
		this.solver = solver;
		this.init = init;
	}

	@Override
	public Collection<? extends ExplState> getInitStates(final ExplPrecision precision) {
		checkNotNull(precision);
		final Set<ExplState> initStates = new HashSet<>();
		boolean moreInitStates;
		solver.push();
		solver.add(PathUtils.unfold(init, 0));
		do {
			moreInitStates = solver.check().boolValue();
			if (moreInitStates) {
				final Valuation nextInitStateVal = PathUtils.extractValuation(solver.getModel(), 0);
				final ExplState nextInitState = precision.mapToAbstractState(nextInitStateVal);
				initStates.add(nextInitState);
				solver.add(PathUtils.unfold(Exprs.Not(nextInitState.toExpr()), 0));
			}
		} while (moreInitStates);
		solver.pop();
		return initStates;
	}

}
