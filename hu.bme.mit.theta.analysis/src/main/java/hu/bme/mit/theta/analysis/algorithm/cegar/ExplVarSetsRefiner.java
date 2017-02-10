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
import hu.bme.mit.theta.analysis.expr.ExprAction;
import hu.bme.mit.theta.analysis.expr.ExprState;
import hu.bme.mit.theta.analysis.expr.ExprTraceChecker;
import hu.bme.mit.theta.analysis.expr.ExprTraceStatus;
import hu.bme.mit.theta.analysis.expr.IndexedVarsRefutation;
import hu.bme.mit.theta.common.ObjectUtils;
import hu.bme.mit.theta.common.logging.Logger;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.Type;

public final class ExplVarSetsRefiner<S extends ExprState, A extends ExprAction>
		implements Refiner<S, A, ExplPrecision> {

	private final ExprTraceChecker<IndexedVarsRefutation> exprTraceChecker;
	private final Logger logger;

	private ExplVarSetsRefiner(final ExprTraceChecker<IndexedVarsRefutation> exprTraceChecker, final Logger logger) {
		this.exprTraceChecker = checkNotNull(exprTraceChecker);
		this.logger = checkNotNull(logger);
	}

	public static <S extends ExprState, A extends ExprAction> ExplVarSetsRefiner<S, A> create(
			final ExprTraceChecker<IndexedVarsRefutation> exprTraceChecker, final Logger logger) {
		return new ExplVarSetsRefiner<>(exprTraceChecker, logger);
	}

	@Override
	public RefinerResult<S, A, ExplPrecision> refine(final ARG<S, A> arg, final ExplPrecision precision) {
		checkNotNull(arg);
		checkNotNull(precision);
		checkArgument(!arg.isSafe());

		final ArgTrace<S, A> cexToConcretize = arg.getCexs().findFirst().get();
		final Trace<S, A> traceToConcretize = cexToConcretize.toTrace();
		logger.writeln("Trace length: ", traceToConcretize.length(), 3, 2);
		logger.writeln("Trace: ", traceToConcretize, 4, 3);

		logger.write("Checking...", 3, 2);
		final ExprTraceStatus<IndexedVarsRefutation> cexStatus = exprTraceChecker.check(traceToConcretize);
		logger.writeln("done: ", cexStatus, 3, 0);

		if (cexStatus.isFeasible()) {
			return RefinerResult.unsafe(traceToConcretize);
		} else if (cexStatus.isInfeasible()) {
			final IndexedVarsRefutation refutation = cexStatus.asInfeasible().getRefutation();
			logger.writeln(refutation, 4, 3);
			final Set<VarDecl<? extends Type>> vars = refutation.getVarSets().getAllVars();
			final ExplPrecision refinedPrecision = precision.refine(vars);
			final int pruneIndex = refutation.getPruneIndex();
			checkState(0 <= pruneIndex && pruneIndex <= cexToConcretize.length());
			logger.writeln("Pruning from index ", pruneIndex, 3, 2);
			final ArgNode<S, A> nodeToPrune = cexToConcretize.node(pruneIndex);
			arg.prune(nodeToPrune);
			return RefinerResult.spurious(refinedPrecision);
		} else {
			throw new IllegalStateException("Unknown status.");
		}
	}

	@Override
	public String toString() {
		return ObjectUtils.toStringBuilder(getClass().getSimpleName()).add(exprTraceChecker).toString();
	}
}
