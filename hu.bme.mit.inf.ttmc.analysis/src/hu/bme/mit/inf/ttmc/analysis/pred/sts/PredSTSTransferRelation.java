package hu.bme.mit.inf.ttmc.analysis.pred.sts;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;
import java.util.HashSet;
import java.util.Set;

import hu.bme.mit.inf.ttmc.analysis.ExprState;
import hu.bme.mit.inf.ttmc.analysis.TransferRelation;
import hu.bme.mit.inf.ttmc.analysis.pred.PredPrecision;
import hu.bme.mit.inf.ttmc.analysis.pred.PredState;
import hu.bme.mit.inf.ttmc.core.expr.Expr;
import hu.bme.mit.inf.ttmc.core.expr.impl.Exprs;
import hu.bme.mit.inf.ttmc.core.type.BoolType;
import hu.bme.mit.inf.ttmc.formalism.sts.STS;
import hu.bme.mit.inf.ttmc.solver.Solver;

public class PredSTSTransferRelation implements TransferRelation<PredState, PredPrecision> {

	private final Solver solver;
	private final STS sts;

	public PredSTSTransferRelation(final STS sts, final Solver solver) {
		this.sts = checkNotNull(sts);
		this.solver = checkNotNull(solver);
	}

	@Override
	public Collection<? extends PredState> getSuccStates(final PredState state, final PredPrecision precision) {
		checkNotNull(state);
		final Set<PredState> succStates = new HashSet<>();
		boolean moreSuccessors;
		do {
			Expr<? extends BoolType> nextSuccExpr = null;
			solver.push();
			for (final Expr<? extends BoolType> pred : state.getPreds())
				solver.add(sts.unroll(pred, 0));
			solver.add(sts.unrollInv(0));
			solver.add(sts.unrollInv(1));
			solver.add(sts.unrollTrans(0));
			for (final ExprState existingSucc : succStates)
				solver.add(sts.unroll(Exprs.Not(existingSucc.asExpr()), 1));

			moreSuccessors = solver.check().boolValue();
			if (moreSuccessors)
				nextSuccExpr = sts.getConcreteState(solver.getModel(), 1).toExpr();

			solver.pop();
			if (moreSuccessors) {
				final Set<Expr<? extends BoolType>> nextSuccPreds = new HashSet<>();
				solver.push();
				solver.add(sts.unroll(nextSuccExpr, 0));
				for (final Expr<? extends BoolType> pred : precision.getPreds()) {
					solver.push();
					solver.add(sts.unroll(pred, 0));
					if (solver.check().boolValue()) {
						nextSuccPreds.add(pred);
					} else {
						nextSuccPreds.add(precision.negate(pred));
					}
					solver.pop();
				}
				solver.pop();
				succStates.add(PredState.create(nextSuccPreds));
			}

		} while (moreSuccessors);
		return succStates;
	}

}
