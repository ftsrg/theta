package hu.bme.mit.inf.ttmc.analysis.pred;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;
import java.util.HashSet;
import java.util.Set;

import hu.bme.mit.inf.ttmc.analysis.FormalismAbstraction;
import hu.bme.mit.inf.ttmc.core.expr.Expr;
import hu.bme.mit.inf.ttmc.core.expr.impl.Exprs;
import hu.bme.mit.inf.ttmc.core.type.BoolType;
import hu.bme.mit.inf.ttmc.formalism.common.Valuation;
import hu.bme.mit.inf.ttmc.formalism.sts.STS;
import hu.bme.mit.inf.ttmc.solver.Solver;

public final class STSPredAbstraction implements FormalismAbstraction<STS, PredState, PredPrecision> {

	private final Solver solver;
	private final STS sts;
	private final Expr<? extends BoolType> negProp;

	public static STSPredAbstraction create(final STS sts, final Solver solver) {
		return new STSPredAbstraction(sts, solver);
	}

	private STSPredAbstraction(final STS sts, final Solver solver) {
		this.sts = checkNotNull(sts);
		this.solver = checkNotNull(solver);
		this.negProp = Exprs.Not(checkNotNull(sts.getProp()));
	}

	@Override
	public Collection<? extends PredState> getStartStates(final PredPrecision precision) {
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
				solver.add(sts.unroll(Exprs.Not(nextInitState.toExpr()), 0));
			}
		} while (moreInitStates);
		solver.pop();

		return initStates;
	}

	@Override
	public Collection<? extends PredState> getSuccStates(final PredState state, final PredPrecision precision) {
		checkNotNull(state);
		checkNotNull(precision);
		final Set<PredState> succStates = new HashSet<>();
		solver.push();
		solver.add(sts.unroll(state.toExpr(), 0));
		solver.add(sts.unrollInv(0));
		solver.add(sts.unrollInv(1));
		solver.add(sts.unrollTrans(0));
		boolean moreSuccStates;
		do {
			moreSuccStates = solver.check().boolValue();
			if (moreSuccStates) {
				final Valuation nextSuccStateVal = sts.getConcreteState(solver.getModel(), 1);

				final PredState nextSuccState = precision.mapToAbstractState(nextSuccStateVal);
				succStates.add(nextSuccState);
				solver.add(sts.unroll(Exprs.Not(nextSuccState.toExpr()), 1));
			}
		} while (moreSuccStates);
		solver.pop();

		return succStates;
	}

	@Override
	public boolean isTarget(final PredState state) {
		solver.push();
		solver.add(sts.unrollInv(0));
		solver.add(sts.unroll(state.toExpr(), 0));
		solver.add(sts.unroll(negProp, 0));
		solver.check();
		final boolean isError = solver.getStatus().boolValue();
		solver.pop();
		return isError;
	}

}
