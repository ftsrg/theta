package hu.bme.mit.theta.xcfa.analysis.impl.interleavings.por;

import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.analysis.algorithm.ARG;
import hu.bme.mit.theta.analysis.algorithm.ArgNode;
import hu.bme.mit.theta.analysis.algorithm.cegar.Refiner;
import hu.bme.mit.theta.analysis.algorithm.cegar.RefinerResult;
import hu.bme.mit.theta.analysis.expr.ExprAction;
import hu.bme.mit.theta.analysis.expr.ExprState;
import hu.bme.mit.theta.analysis.expr.refinement.*;
import hu.bme.mit.theta.common.logging.Logger;
import hu.bme.mit.theta.core.decl.Decl;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.xcfa.analysis.impl.interleavings.XcfaState;

import java.util.HashSet;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

public final class AbstractPorSingleExprtTraceRefiner<S extends ExprState, A extends ExprAction, P extends Prec, R extends Refutation>
		implements Refiner<S, A, P> {

	private final SingleExprTraceRefiner<S, A, P, R> refiner;

	private final PruneStrategy pruneStrategy;

	private final NodePruner<S, A> pruner;

	private final Map<Decl<? extends Type>, Set<XcfaState<?>>> ignoredVariableRegistry;

	private AbstractPorSingleExprtTraceRefiner(final SingleExprTraceRefiner<S, A, P, R> refiner,
											   final PruneStrategy pruneStrategy,
											   final NodePruner<S, A> pruner,
											   final Map<Decl<? extends Type>, Set<XcfaState<?>>> ignoredVariableRegistry) {
		this.refiner = refiner;
		this.pruneStrategy = pruneStrategy;
		this.pruner = pruner;
		this.ignoredVariableRegistry = ignoredVariableRegistry;
	}

	public static <S extends ExprState, A extends ExprAction, P extends Prec, R extends Refutation> AbstractPorSingleExprtTraceRefiner<S, A, P, R> create(
			final ExprTraceChecker<R> exprTraceChecker, final PrecRefiner<S, A, P, R> precRefiner,
			final PruneStrategy pruneStrategy, final Logger logger, final NodePruner<S, A> nodePruner,
			final Map<Decl<? extends Type>, Set<XcfaState<?>>> ignoredVariableRegistry) {
		return new AbstractPorSingleExprtTraceRefiner<>(
				SingleExprTraceRefiner.create(exprTraceChecker, precRefiner, pruneStrategy, logger, nodePruner),
				pruneStrategy, nodePruner, ignoredVariableRegistry
		);
	}

	@Override
	public RefinerResult<S, A, P> refine(final ARG<S, A> arg, final P prec) {
		final RefinerResult<S, A, P> result = refiner.refine(arg, prec);
		if (result.isUnsafe() || pruneStrategy != PruneStrategy.LAZY) return result;

		final P newPrec = result.asSpurious().getRefinedPrec();
		final Set<Decl<? extends Type>> newlyAddedVars = new HashSet<>(newPrec.getUsedVars());
		newlyAddedVars.removeAll(prec.getUsedVars());

		newlyAddedVars.forEach(newVar -> {
			if (ignoredVariableRegistry.containsKey(newVar)) {
				Set<ArgNode<S, A>> nodesToPrune = ignoredVariableRegistry.get(newVar).stream().flatMap(stateToPrune ->
						arg.getNodes().filter(node -> node.getState().equals(stateToPrune)) // TODO one state can be in one ARG node?
				).collect(Collectors.toSet());
				nodesToPrune.forEach(node -> pruner.prune(arg, node));
				ignoredVariableRegistry.remove(newVar);
			}
		});

		return result;
	}
}
