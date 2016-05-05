package hu.bme.mit.inf.ttmc.analysis.pred.sts;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;
import java.util.HashSet;
import java.util.Set;

import hu.bme.mit.inf.ttmc.analysis.ExprState;
import hu.bme.mit.inf.ttmc.analysis.InitStates;
import hu.bme.mit.inf.ttmc.analysis.pred.PredPrecision;
import hu.bme.mit.inf.ttmc.analysis.pred.PredState;
import hu.bme.mit.inf.ttmc.core.expr.Expr;
import hu.bme.mit.inf.ttmc.core.expr.impl.Exprs;
import hu.bme.mit.inf.ttmc.core.type.BoolType;
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
		final Set<PredState> initStates = new HashSet<>();
		boolean moreInitialStates;

		do {
			Expr<? extends BoolType> nextInitStateExpr = null;
			solver.push();
			solver.add(sts.unrollInit(0));
			solver.add(sts.unrollInv(0));
			for (final ExprState existingInit : initStates)
				solver.add(sts.unroll(Exprs.Not(existingInit.asExpr()), 0));

			moreInitialStates = solver.check().boolValue();
			if (moreInitialStates) {
				nextInitStateExpr = sts.getConcreteState(solver.getModel(), 0).toExpr();
			}

			solver.pop();
			if (moreInitialStates) {
				final Set<Expr<? extends BoolType>> nextInitStatePreds = new HashSet<>();
				solver.push();
				solver.add(sts.unroll(nextInitStateExpr, 0));
				for (final Expr<? extends BoolType> pred : precision.getPreds()) {
					solver.push();
					solver.add(sts.unroll(pred, 0));
					if (solver.check().boolValue()) {
						nextInitStatePreds.add(pred);
					} else {
						nextInitStatePreds.add(precision.negate(pred));
					}
					solver.pop();
				}
				solver.pop();
				initStates.add(PredState.create(nextInitStatePreds));
			}
		} while (moreInitialStates);
		return initStates;
	}

}
