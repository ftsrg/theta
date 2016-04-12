package hu.bme.mit.inf.ttmc.cegar.visiblecegar.steps.refinement;

import java.util.Collection;
import java.util.List;

import hu.bme.mit.inf.ttmc.cegar.common.data.ConcreteTrace;
import hu.bme.mit.inf.ttmc.cegar.common.steps.AbstractCEGARStep;
import hu.bme.mit.inf.ttmc.cegar.common.utils.visualization.Visualizer;
import hu.bme.mit.inf.ttmc.cegar.visiblecegar.data.VisibleAbstractState;
import hu.bme.mit.inf.ttmc.cegar.visiblecegar.data.VisibleAbstractSystem;
import hu.bme.mit.inf.ttmc.common.logging.Logger;
import hu.bme.mit.inf.ttmc.core.expr.Expr;
import hu.bme.mit.inf.ttmc.core.type.Type;
import hu.bme.mit.inf.ttmc.formalism.common.decl.VarDecl;
import hu.bme.mit.inf.ttmc.formalism.sts.STS;
import hu.bme.mit.inf.ttmc.formalism.utils.impl.FormalismUtils;
import hu.bme.mit.inf.ttmc.solver.ItpMarker;
import hu.bme.mit.inf.ttmc.solver.ItpPattern;
import hu.bme.mit.inf.ttmc.solver.ItpSolver;

public class CraigItpVarCollector extends AbstractCEGARStep implements VarCollector {

	public CraigItpVarCollector(final Logger logger, final Visualizer visualizer) {
		super(logger, visualizer);
	}

	@Override
	public Collection<VarDecl<? extends Type>> collectVars(final VisibleAbstractSystem system,
			final List<VisibleAbstractState> abstractCounterEx, final ConcreteTrace concreteTrace) {
		final ItpSolver interpolatingSolver = system.getManager().getSolverFactory().createItpSolver();
		final int traceLength = concreteTrace.size();
		assert (traceLength < abstractCounterEx.size());

		final ItpMarker A = interpolatingSolver.createMarker();
		final ItpMarker B = interpolatingSolver.createMarker();
		final ItpPattern pattern = interpolatingSolver.createBinPattern(A, B);

		final STS sts = system.getSTS();

		interpolatingSolver.push();
		// The first formula (A) describes the dead-end states
		interpolatingSolver.add(A, sts.unrollInit(0));
		for (int i = 0; i < traceLength; ++i) {
			// Expression of the abstract state
			interpolatingSolver.add(A, sts.unroll(abstractCounterEx.get(i).getExpression(), i));

			if (i > 0) {
				// Transition relation
				interpolatingSolver.add(A, sts.unrollTrans(i - 1));
			}

			// Invariants
			interpolatingSolver.add(A, sts.unrollInv(i));

		}
		// The second formula (B) describes the bad states, which are states
		// with
		// transitions to the next abstract state

		// Expression of the next abstract state
		interpolatingSolver.add(B, sts.unroll(abstractCounterEx.get(traceLength).getExpression(), traceLength));
		// Invariants for the next abstract state
		interpolatingSolver.add(B, sts.unrollInv(traceLength));
		// Transition to the next abstract state
		interpolatingSolver.add(B, sts.unrollTrans(traceLength - 1));

		// Since A and B is unsatisfiable (otherwise there would be a concrete
		// counterexample),
		// an invariant I must exist with A -> I, I and B unsat and I contains
		// only variables with
		// the index (traceLength-1), thus splitting the failure state
		interpolatingSolver.check();
		final Expr<? extends Type> interpolant = sts.foldin(interpolatingSolver.getInterpolant(pattern).eval(A),
				traceLength - 1);

		logger.writeln("Interpolant: " + interpolant, 4, 0);
		interpolatingSolver.pop();
		return FormalismUtils.collectVars(interpolant);
	}

	@Override
	public String toString() {
		return "craigItpVarColl";
	}
}
