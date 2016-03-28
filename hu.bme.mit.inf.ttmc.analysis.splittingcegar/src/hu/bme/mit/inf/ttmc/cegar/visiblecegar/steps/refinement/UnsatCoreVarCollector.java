package hu.bme.mit.inf.ttmc.cegar.visiblecegar.steps.refinement;

import java.util.Collection;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import hu.bme.mit.inf.ttmc.cegar.common.data.ConcreteTrace;
import hu.bme.mit.inf.ttmc.cegar.common.steps.AbstractCEGARStep;
import hu.bme.mit.inf.ttmc.cegar.common.utils.visualization.Visualizer;
import hu.bme.mit.inf.ttmc.cegar.visiblecegar.data.VisibleAbstractState;
import hu.bme.mit.inf.ttmc.cegar.visiblecegar.data.VisibleAbstractSystem;
import hu.bme.mit.inf.ttmc.common.logging.Logger;
import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.solver.Solver;
import hu.bme.mit.inf.ttmc.constraint.solver.SolverStatus;
import hu.bme.mit.inf.ttmc.constraint.type.BoolType;
import hu.bme.mit.inf.ttmc.constraint.type.Type;
import hu.bme.mit.inf.ttmc.formalism.common.decl.VarDecl;
import hu.bme.mit.inf.ttmc.formalism.sts.STSUnroller;
import hu.bme.mit.inf.ttmc.formalism.utils.impl.FormalismUtils;

public class UnsatCoreVarCollector extends AbstractCEGARStep implements VarCollector {

	public UnsatCoreVarCollector(final Logger logger, final Visualizer visualizer) {
		super(logger, visualizer);
	}

	@Override
	public Collection<VarDecl<? extends Type>> collectVars(final VisibleAbstractSystem system, final List<VisibleAbstractState> abstractCounterEx,
			final ConcreteTrace concreteCounterEx) {

		final Solver solver = system.getManager().getSolverFactory().createSolver(true, true);
		final int traceLength = concreteCounterEx.size();
		assert (traceLength < abstractCounterEx.size());

		final STSUnroller unroller = system.getUnroller();

		solver.push();
		solver.track(unroller.init(0));
		for (int i = 0; i < traceLength + 1; ++i) {
			for (final Expr<? extends BoolType> label : abstractCounterEx.get(i).getExpression().getOps())
				solver.track(unroller.unroll(label, i));
			if (i > 0)
				solver.track(unroller.trans(i - 1));
			solver.track(unroller.inv(i));
		}

		solver.check();

		assert (solver.getStatus() == SolverStatus.UNSAT);

		final Set<VarDecl<? extends Type>> vars = new HashSet<>();

		for (final Expr<? extends BoolType> uc : solver.getUnsatCore())
			FormalismUtils.collectVars(unroller.foldin(uc, 0), vars);

		solver.pop();

		return vars;
	}

}
