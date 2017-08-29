package hu.bme.mit.theta.analysis.expl;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.And;

import java.util.Collection;
import java.util.Collections;
import java.util.List;

import hu.bme.mit.theta.analysis.TransferFunction;
import hu.bme.mit.theta.analysis.expl.ExplStmtSuccEvaluator.EvalResult;
import hu.bme.mit.theta.analysis.expr.ExprStates;
import hu.bme.mit.theta.core.Expr;
import hu.bme.mit.theta.core.stmt.Stmt;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.utils.StmtUnfoldResult;
import hu.bme.mit.theta.core.utils.StmtUtils;
import hu.bme.mit.theta.core.utils.VarIndexing;
import hu.bme.mit.theta.solver.Solver;

public final class ExplStmtTransferFunction implements TransferFunction<ExplState, StmtAction, ExplPrec> {

	private final Solver solver;
	private final int maxStatesFromSolver;

	private ExplStmtTransferFunction(final Solver solver, final int maxStatesFromSolver) {
		checkArgument(maxStatesFromSolver >= 0, "Max. states from solver must be non-negative.");
		this.solver = checkNotNull(solver);
		this.maxStatesFromSolver = maxStatesFromSolver;
	}

	public static ExplStmtTransferFunction create(final Solver solver, final int maxStatesFromSolver) {
		return new ExplStmtTransferFunction(solver, maxStatesFromSolver);
	}

	@Override
	public Collection<? extends ExplState> getSuccStates(final ExplState state, final StmtAction action,
			final ExplPrec prec) {
		return getSuccStates(state, action.getStmts(), prec);
	}

	Collection<? extends ExplState> getSuccStates(final ExplState state, final List<Stmt> stmts, final ExplPrec prec) {
		boolean triedSolver = false;
		ExplState running = state;

		for (int i = 0; i < stmts.size(); i++) {
			final Stmt stmt = stmts.get(i);
			final EvalResult evalResult = ExplStmtSuccEvaluator.evalSucc(running, stmt);
			if (!evalResult.isPrecise() && !triedSolver && maxStatesFromSolver > 0) {
				triedSolver = true;
				final List<Stmt> remainingStmts = stmts.subList(i, stmts.size());
				final StmtUnfoldResult toExprResult = StmtUtils.toExpr(remainingStmts, VarIndexing.all(0));
				final Expr<BoolType> expr = And(running.toExpr(), And(toExprResult.getExprs()));
				final VarIndexing nextIdx = toExprResult.getIndexing();
				// We query (max + 1) states from the solver to see if there would be more than max
				final Collection<ExplState> succStates = ExprStates.createStatesForExpr(solver, expr, 0,
						prec::createState, nextIdx, maxStatesFromSolver + 1);
				if (succStates.size() <= maxStatesFromSolver) {
					return succStates;
				}
			}
			running = evalResult.getState();
		}

		if (running.isBottom()) {
			return Collections.emptyList();
		} else {
			final ExplState abstracted = prec.createState(running);
			return Collections.singleton(abstracted);
		}
	}

}
