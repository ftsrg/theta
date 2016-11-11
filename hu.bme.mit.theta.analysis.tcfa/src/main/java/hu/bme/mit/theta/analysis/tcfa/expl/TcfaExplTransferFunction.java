package hu.bme.mit.theta.analysis.tcfa.expl;

import static com.google.common.base.Preconditions.checkNotNull;
import static java.util.stream.Collectors.toList;

import java.util.Collection;
import java.util.List;

import com.google.common.collect.ImmutableSet;

import hu.bme.mit.theta.analysis.TransferFunction;
import hu.bme.mit.theta.analysis.expl.ExplPrecision;
import hu.bme.mit.theta.analysis.expl.ExplState;
import hu.bme.mit.theta.analysis.tcfa.TcfaAction;
import hu.bme.mit.theta.analysis.tcfa.TcfaExpr;
import hu.bme.mit.theta.analysis.tcfa.TcfaExpr.DataExpr;
import hu.bme.mit.theta.analysis.tcfa.TcfaStmt;
import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.expr.impl.Exprs;
import hu.bme.mit.theta.core.model.impl.Valuation;
import hu.bme.mit.theta.core.stmt.Stmt;
import hu.bme.mit.theta.core.type.BoolType;
import hu.bme.mit.theta.core.utils.impl.PathUtils;
import hu.bme.mit.theta.core.utils.impl.StmtToExprResult;
import hu.bme.mit.theta.core.utils.impl.StmtUtils;
import hu.bme.mit.theta.core.utils.impl.VarIndexing;
import hu.bme.mit.theta.solver.Solver;

public final class TcfaExplTransferFunction implements TransferFunction<ExplState, TcfaAction, ExplPrecision> {

	private final Solver solver;

	private TcfaExplTransferFunction(final Solver solver) {
		this.solver = checkNotNull(solver);
	}

	public static TcfaExplTransferFunction create(final Solver solver) {
		return new TcfaExplTransferFunction(solver);
	}

	@Override
	public Collection<ExplState> getSuccStates(final ExplState state, final TcfaAction action,
			final ExplPrecision precision) {

		final ImmutableSet.Builder<ExplState> builder = ImmutableSet.builder();

		solver.push();
		solver.add(PathUtils.unfold(state.toExpr(), 0));

		final List<Stmt> stmts = action.getTcfaStmts().stream().filter(TcfaStmt::isDataStmt).map(TcfaStmt::getStmt)
				.collect(toList());
		final StmtToExprResult transformResult = StmtUtils.toExpr(stmts, VarIndexing.all(0));
		final Collection<? extends Expr<? extends BoolType>> stmtExprs = transformResult.getExprs().stream()
				.map(e -> PathUtils.unfold(e, 0)).collect(toList());
		final VarIndexing indexing = transformResult.getIndexing();

		solver.add(stmtExprs);

		for (final TcfaExpr invar : action.getTargetInvars()) {
			if (invar.isDataExpr()) {
				final DataExpr dataExpr = invar.asDataExpr();
				final Expr<? extends BoolType> expr = dataExpr.getExpr();
				solver.add(PathUtils.unfold(expr, indexing));
			}
		}

		boolean moreSuccStates;
		do {
			moreSuccStates = solver.check().isSat();
			if (moreSuccStates) {
				final Valuation nextSuccStateVal = PathUtils.extractValuation(solver.getModel(), indexing);
				final ExplState nextSuccState = precision.createState(nextSuccStateVal);
				builder.add(nextSuccState);
				solver.add(PathUtils.unfold(Exprs.Not(nextSuccState.toExpr()), indexing));
			}
		} while (moreSuccStates);
		solver.pop();

		return builder.build();
	}

}
