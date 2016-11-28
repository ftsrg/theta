package hu.bme.mit.theta.analysis.algorithm.cegar;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;
import static com.google.common.base.Preconditions.checkState;

import java.util.Set;

import hu.bme.mit.theta.analysis.Trace;
import hu.bme.mit.theta.analysis.algorithm.ARG;
import hu.bme.mit.theta.analysis.algorithm.ArgNode;
import hu.bme.mit.theta.analysis.algorithm.ArgTrace;
import hu.bme.mit.theta.analysis.expl.ExplPrecision;
import hu.bme.mit.theta.analysis.expl.ExplState;
import hu.bme.mit.theta.analysis.expr.ExprAction;
import hu.bme.mit.theta.analysis.expr.ExprTraceChecker;
import hu.bme.mit.theta.analysis.expr.ExprTraceStatus2;
import hu.bme.mit.theta.analysis.expr.IndexedVarsRefutation;
import hu.bme.mit.theta.common.logging.Logger;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.Type;

public final class ExplVarSetsRefiner<A extends ExprAction> implements Refiner<ExplState, A, ExplPrecision> {

	private final ExprTraceChecker<IndexedVarsRefutation> exprTraceChecker;
	private final Logger logger;

	private ExplVarSetsRefiner(final ExprTraceChecker<IndexedVarsRefutation> exprTraceChecker, final Logger logger) {
		this.exprTraceChecker = checkNotNull(exprTraceChecker);
		this.logger = checkNotNull(logger);
	}

	public static <A extends ExprAction> ExplVarSetsRefiner<A> create(
			final ExprTraceChecker<IndexedVarsRefutation> exprTraceChecker, final Logger logger) {
		return new ExplVarSetsRefiner<>(exprTraceChecker, logger);
	}

	@Override
	public RefinerResult<ExplState, A, ExplPrecision> refine(final ARG<ExplState, A> arg,
			final ExplPrecision precision) {
		checkNotNull(arg);
		checkNotNull(precision);
		checkArgument(!arg.isSafe());

		final ArgTrace<ExplState, A> cexToConcretize = arg.getCexs().findFirst().get();
		final Trace<ExplState, A> traceToConcretize = cexToConcretize.toTrace();
		logger.writeln("Trace: ", traceToConcretize, 4, 3);

		final ExprTraceStatus2<IndexedVarsRefutation> cexStatus = exprTraceChecker.check(traceToConcretize);

		if (cexStatus.isFeasible()) {
			return RefinerResult.unsafe(traceToConcretize);
		} else if (cexStatus.isInfeasible()) {
			final IndexedVarsRefutation refutation = cexStatus.asInfeasible().getRefutation();
			final Set<VarDecl<? extends Type>> vars = refutation.getVarSets().getAllVars();
			final ExplPrecision refinedPrecision = precision.refine(vars);
			final int pruneIndex = refutation.getPruneIndex();
			checkState(0 <= pruneIndex && pruneIndex <= cexToConcretize.length());
			final ArgNode<ExplState, A> nodeToPrune = cexToConcretize.node(pruneIndex);
			arg.prune(nodeToPrune);
			return RefinerResult.spurious(refinedPrecision);
		} else {
			throw new IllegalStateException("Unknown status.");
		}
	}

}
