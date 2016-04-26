package hu.bme.mit.inf.ttmc.analysis.pred;

import java.util.Collection;
import java.util.HashSet;
import java.util.Set;

import hu.bme.mit.inf.ttmc.analysis.InitStates;
import hu.bme.mit.inf.ttmc.core.expr.AndExpr;
import hu.bme.mit.inf.ttmc.core.expr.Expr;
import hu.bme.mit.inf.ttmc.core.expr.impl.Exprs;
import hu.bme.mit.inf.ttmc.core.type.BoolType;
import hu.bme.mit.inf.ttmc.formalism.sts.STS;
import hu.bme.mit.inf.ttmc.solver.Solver;

public class PredSTSInitStates implements InitStates<PredState> {

	private final Solver solver;
	private final STS sts;
	private final Set<Expr<? extends BoolType>> preds;

	public PredSTSInitStates(final STS sts, final Collection<? extends Expr<? extends BoolType>> preds, final Solver solver) {
		this.sts = sts;
		this.solver = solver;
		this.preds = new HashSet<>(preds);
	}

	@Override
	public Collection<? extends PredState> get() {
		final Set<PredState> initStates = new HashSet<>();
		while (true) {
			AndExpr nextInitStateExpr = null;
			solver.push();
			solver.add(sts.unrollInit(0));
			solver.add(sts.unrollInv(0));
			for (final PredState existingInit : initStates)
				solver.add(sts.unroll(Exprs.Not(Exprs.And(existingInit.getPreds())), 0));
			if (solver.check().boolValue())
				nextInitStateExpr = sts.getConcreteState(solver.getModel(), 0);
			solver.pop();
			if (nextInitStateExpr != null) {
				final Set<Expr<? extends BoolType>> nextInitStatePreds = new HashSet<>();
				solver.push();
				solver.add(sts.unroll(nextInitStateExpr, 0));
				for (final Expr<? extends BoolType> pred : preds) {
					solver.push();
					solver.add(sts.unroll(pred, 0));
					if (solver.check().boolValue()) {
						nextInitStatePreds.add(pred);
					} else {
						nextInitStatePreds.add(Exprs.Not(pred));
					}
					solver.pop();
				}
				solver.pop();
				initStates.add(PredState.create(nextInitStatePreds, solver));
			} else {
				break;
			}
		}
		return initStates;
	}

}
