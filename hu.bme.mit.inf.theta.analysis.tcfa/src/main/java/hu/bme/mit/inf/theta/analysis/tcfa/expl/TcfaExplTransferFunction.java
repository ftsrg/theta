package hu.bme.mit.inf.theta.analysis.tcfa.expl;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;

import com.google.common.collect.ImmutableSet;

import hu.bme.mit.inf.theta.analysis.TransferFunction;
import hu.bme.mit.inf.theta.analysis.expl.ExplPrecision;
import hu.bme.mit.inf.theta.analysis.expl.ExplState;
import hu.bme.mit.inf.theta.analysis.tcfa.TcfaAction;
import hu.bme.mit.inf.theta.core.expr.Expr;
import hu.bme.mit.inf.theta.core.expr.impl.Exprs;
import hu.bme.mit.inf.theta.core.type.BoolType;
import hu.bme.mit.inf.theta.formalism.common.Valuation;
import hu.bme.mit.inf.theta.formalism.utils.PathUtils;
import hu.bme.mit.inf.theta.formalism.utils.StmtUnroller;
import hu.bme.mit.inf.theta.formalism.utils.VarIndexes;
import hu.bme.mit.inf.theta.formalism.utils.StmtUnroller.StmtToExprResult;
import hu.bme.mit.inf.theta.solver.Solver;

final class TcfaExplTransferFunction implements TransferFunction<ExplState, TcfaAction, ExplPrecision> {

	private final Solver solver;

	TcfaExplTransferFunction(final Solver solver) {
		this.solver = checkNotNull(solver);
	}

	@Override
	public Collection<ExplState> getSuccStates(final ExplState state, final TcfaAction action,
			final ExplPrecision precision) {

		final ImmutableSet.Builder<ExplState> builder = ImmutableSet.builder();

		solver.push();
		solver.add(PathUtils.unfold(state.toExpr(), 0));

		final StmtToExprResult transformResult = StmtUnroller.transform(action.getDataStmts(), VarIndexes.all(0));
		final Collection<? extends Expr<? extends BoolType>> stmtExprs = transformResult.getExprs();
		final VarIndexes indexes = transformResult.getIndexes();

		solver.add(stmtExprs);

		for (final Expr<? extends BoolType> invar : action.getTargetDataInvars()) {
			solver.add(PathUtils.unfold(invar, indexes));
		}

		boolean moreSuccStates;
		do {
			moreSuccStates = solver.check().boolValue();
			if (moreSuccStates) {
				final Valuation nextSuccStateVal = PathUtils.extractValuation(solver.getModel(), indexes);
				final ExplState nextSuccState = precision.mapToAbstractState(nextSuccStateVal);
				builder.add(nextSuccState);
				solver.add(PathUtils.unfold(Exprs.Not(nextSuccState.toExpr()), indexes));
			}
		} while (moreSuccStates);
		solver.pop();

		return builder.build();
	}

}
