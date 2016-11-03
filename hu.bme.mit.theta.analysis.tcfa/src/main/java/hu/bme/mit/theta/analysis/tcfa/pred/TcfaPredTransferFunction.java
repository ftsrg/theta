package hu.bme.mit.theta.analysis.tcfa.pred;

import static com.google.common.base.Preconditions.checkNotNull;
import static java.util.stream.Collectors.toList;

import java.util.Collection;

import com.google.common.collect.ImmutableSet;

import hu.bme.mit.theta.analysis.TransferFunction;
import hu.bme.mit.theta.analysis.pred.PredPrecision;
import hu.bme.mit.theta.analysis.pred.PredState;
import hu.bme.mit.theta.analysis.tcfa.TcfaAction;
import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.expr.impl.Exprs;
import hu.bme.mit.theta.core.model.impl.Valuation;
import hu.bme.mit.theta.core.type.BoolType;
import hu.bme.mit.theta.core.utils.impl.PathUtils;
import hu.bme.mit.theta.core.utils.impl.StmtToExprResult;
import hu.bme.mit.theta.core.utils.impl.StmtUtils;
import hu.bme.mit.theta.core.utils.impl.VarIndexing;
import hu.bme.mit.theta.solver.Solver;

final class TcfaPredTransferFunction implements TransferFunction<PredState, TcfaAction, PredPrecision> {

	final Solver solver;

	TcfaPredTransferFunction(final Solver solver) {
		this.solver = checkNotNull(solver);
	}

	@Override
	public Collection<PredState> getSuccStates(final PredState state, final TcfaAction action,
			final PredPrecision precision) {
		checkNotNull(state);
		checkNotNull(precision);

		final ImmutableSet.Builder<PredState> builder = ImmutableSet.builder();
		solver.push();

		solver.add(PathUtils.unfold(state.toExpr(), 0));
		for (final Expr<? extends BoolType> invar : action.getSourceDataInvars()) {
			solver.add(PathUtils.unfold(invar, 0));
		}

		final StmtToExprResult transformResult = StmtUtils.toExpr(action.getDataStmts(), VarIndexing.all(0));
		final Collection<? extends Expr<? extends BoolType>> stmtExprs = transformResult.getExprs().stream()
				.map(e -> PathUtils.unfold(e, 0)).collect(toList());
		final VarIndexing indexing = transformResult.getIndexing();

		solver.add(stmtExprs);

		for (final Expr<? extends BoolType> invar : action.getTargetDataInvars()) {
			solver.add(PathUtils.unfold(invar, indexing));
		}

		boolean moreSuccStates;
		do {
			moreSuccStates = solver.check().isSat();
			if (moreSuccStates) {
				final Valuation nextSuccStateVal = PathUtils.extractValuation(solver.getModel(), indexing);

				final PredState nextSuccState = precision.createState(nextSuccStateVal);
				builder.add(nextSuccState);
				solver.add(PathUtils.unfold(Exprs.Not(nextSuccState.toExpr()), indexing));
			}
		} while (moreSuccStates);
		solver.pop();

		return builder.build();
	}
}
