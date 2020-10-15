package hu.bme.mit.theta.analysis.prod2.prod2explpred;

import hu.bme.mit.theta.analysis.expl.ExplPrec;
import hu.bme.mit.theta.analysis.expl.ExplState;
import hu.bme.mit.theta.analysis.pred.PredPrec;
import hu.bme.mit.theta.analysis.pred.PredState;
import hu.bme.mit.theta.analysis.prod2.Prod2Prec;
import hu.bme.mit.theta.analysis.prod2.Prod2State;
import hu.bme.mit.theta.analysis.prod2.StrengtheningOperator;
import hu.bme.mit.theta.core.utils.PathUtils;
import hu.bme.mit.theta.solver.Solver;
import hu.bme.mit.theta.solver.utils.WithPushPop;

import java.util.Collection;
import java.util.HashSet;
import java.util.Set;

public final class Prod2ExplPredStrengtheningOperator implements StrengtheningOperator<ExplState, PredState, ExplPrec, PredPrec> {

	private final Solver solver;

	private Prod2ExplPredStrengtheningOperator(final Solver solver) {
		this.solver = solver;
	}

	public static Prod2ExplPredStrengtheningOperator create(final Solver solver) {
		return new Prod2ExplPredStrengtheningOperator(solver);
	}

	@Override
	public Collection<Prod2State<ExplState, PredState>> strengthen(Collection<Prod2State<ExplState, PredState>> prod2States, Prod2Prec<ExplPrec, PredPrec> prec) {

		Set<Prod2State<ExplState, PredState>> validStates = new HashSet<>();

		for (Prod2State<ExplState, PredState> prod2State : prod2States) {

			try (WithPushPop wp = new WithPushPop(solver)) {
				solver.add(PathUtils.unfold(prod2State.getState1().toExpr(), 0));
				solver.add(PathUtils.unfold(prod2State.getState2().toExpr(), 0));
				var result = solver.check();
				if (result.isSat()) {
					validStates.add(prod2State);
				}
			}

		}
		if (validStates.size() < prod2States.size()) {
			var removed = new HashSet<>();
			for (var state : prod2States) {
				if (!validStates.contains(state)) removed.add(state);
			}
		}

		return validStates;
	}
}

