package hu.bme.mit.inf.ttmc.analysis.expl;

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
import hu.bme.mit.inf.ttmc.formalism.utils.impl.FormalismUtils;
import hu.bme.mit.inf.ttmc.solver.Solver;

public class STSExplAbstraction implements FormalismAbstraction<ExplState, ExplPrecision> {

	private final Solver solver;
	private final STS sts;
	private final Expr<? extends BoolType> negProp;

	public STSExplAbstraction(final STS sts, final Solver solver) {
		this.solver = checkNotNull(solver);
		this.sts = checkNotNull(sts);
		this.negProp = Exprs.Not(sts.getProp());
	}

	@Override
	public Collection<? extends ExplState> getStartStates(final ExplPrecision precision) {
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
				final ExplState nextInitState = precision.mapToAbstractState(nextInitStateVal);
				initStates.add(nextInitState);
				solver.add(sts.unroll(Exprs.Not(nextInitState.asExpr()), 0));
			}
		} while (moreInitStates);
		solver.pop();
		return initStates;
	}

	@Override
	public Collection<? extends ExplState> getSuccStates(final ExplState state, final ExplPrecision precision) {
		checkNotNull(state);
		checkNotNull(precision);
		final Set<ExplState> succStates = new HashSet<>();
		solver.push();
		solver.add(sts.unroll(state.asExpr(), 0));
		solver.add(sts.unrollInv(0));
		solver.add(sts.unrollInv(1));
		solver.add(sts.unrollTrans(0));
		boolean moreSuccStates;
		do {
			moreSuccStates = solver.check().boolValue();
			if (moreSuccStates) {
				final Valuation nextSuccStateVal = sts.getConcreteState(solver.getModel(), 1);
				final ExplState nextSuccState = precision.mapToAbstractState(nextSuccStateVal);
				succStates.add(nextSuccState);
				solver.add(sts.unroll(Exprs.Not(nextSuccState.asExpr()), 1));
			}

		} while (moreSuccStates);
		solver.pop();

		return succStates;
	}

	@Override
	public boolean isTarget(final ExplState state) {
		final Expr<? extends BoolType> simplified = FormalismUtils.simplify(negProp, state);
		if (simplified.equals(Exprs.True()) || simplified.equals(Exprs.False())) {
			return simplified.equals(Exprs.True());
		} else {
			solver.push();
			solver.add(sts.unrollInv(0));
			solver.add(sts.unroll(simplified, 0));
			solver.check();
			final boolean isError = solver.getStatus().boolValue();
			solver.pop();
			return isError;
		}
	}

}
