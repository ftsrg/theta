package hu.bme.mit.inf.ttmc.analysis.sts.pred;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;

import hu.bme.mit.inf.ttmc.analysis.TargetPredicate;
import hu.bme.mit.inf.ttmc.analysis.pred.PredState;
import hu.bme.mit.inf.ttmc.core.expr.Expr;
import hu.bme.mit.inf.ttmc.core.expr.impl.Exprs;
import hu.bme.mit.inf.ttmc.core.type.BoolType;
import hu.bme.mit.inf.ttmc.formalism.sts.STS;
import hu.bme.mit.inf.ttmc.formalism.utils.PathUtils;
import hu.bme.mit.inf.ttmc.solver.Solver;

public class STSPredTargetPredicate implements TargetPredicate<PredState> {

	private final Expr<? extends BoolType> target;
	private final Collection<Expr<? extends BoolType>> invar;
	private final Solver solver;

	public STSPredTargetPredicate(final STS sts, final Solver solver) {
		final Expr<? extends BoolType> prop = sts.getProp();
		this.target = Exprs.Not(checkNotNull(prop));
		this.invar = checkNotNull(sts.getInvar());
		this.solver = checkNotNull(solver);
	}

	@Override
	public boolean isTargetState(final PredState state) {
		solver.push();
		solver.add(PathUtils.unfold(state.toExpr(), 0));
		// TODO: optimization: cache the unrolled target and invar for 0
		solver.add(PathUtils.unfold(target, 0));
		invar.stream().forEach(i -> solver.add(PathUtils.unfold(i, 0)));
		solver.check();
		final boolean isError = solver.getStatus().boolValue();
		solver.pop();
		return isError;
	}

}
