package hu.bme.mit.theta.splittingcegar.visible.steps.refinement;

import java.util.Collection;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import hu.bme.mit.theta.common.logging.Logger;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.utils.ExprUtils;
import hu.bme.mit.theta.core.utils.PathUtils;
import hu.bme.mit.theta.formalism.sts.STS;
import hu.bme.mit.theta.solver.Solver;
import hu.bme.mit.theta.solver.SolverStatus;
import hu.bme.mit.theta.splittingcegar.common.data.ConcreteTrace;
import hu.bme.mit.theta.splittingcegar.common.data.SolverWrapper;
import hu.bme.mit.theta.splittingcegar.common.data.StopHandler;
import hu.bme.mit.theta.splittingcegar.common.steps.AbstractCEGARStep;
import hu.bme.mit.theta.splittingcegar.common.utils.visualization.Visualizer;
import hu.bme.mit.theta.splittingcegar.visible.data.VisibleAbstractState;
import hu.bme.mit.theta.splittingcegar.visible.data.VisibleAbstractSystem;

public class UnsatCoreVarCollector extends AbstractCEGARStep implements VarCollector {

	public UnsatCoreVarCollector(final SolverWrapper solvers, final StopHandler stopHandler, final Logger logger,
			final Visualizer visualizer) {
		super(solvers, stopHandler, logger, visualizer);
	}

	@Override
	public Collection<VarDecl<? extends Type>> collectVars(final VisibleAbstractSystem system,
			final List<VisibleAbstractState> abstractCounterEx, final ConcreteTrace concreteCounterEx) {

		final int traceLength = concreteCounterEx.size();
		assert (traceLength < abstractCounterEx.size());

		final STS sts = system.getSTS();
		final Solver solver = solvers.getSolver();

		solver.push();
		solver.track(PathUtils.unfold(sts.getInit(), 0));
		for (int i = 0; i < traceLength + 1; ++i) {
			// TODO: if the expression is an AND, are the operands added
			// separately?
			solver.track(PathUtils.unfold(abstractCounterEx.get(i).getValuation().toExpr(), i));

			if (i > 0)
				solver.track(PathUtils.unfold(sts.getTrans(), i - 1));
		}

		solver.check();

		assert (solver.getStatus() == SolverStatus.UNSAT);

		final Set<VarDecl<? extends Type>> vars = new HashSet<>();

		for (final Expr<BoolType> uc : solver.getUnsatCore())
			ExprUtils.collectVars(PathUtils.foldin(uc, 0), vars);

		solver.pop();

		return vars;
	}

}
