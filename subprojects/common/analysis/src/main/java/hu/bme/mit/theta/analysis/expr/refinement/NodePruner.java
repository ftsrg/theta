package hu.bme.mit.theta.analysis.expr.refinement;

import hu.bme.mit.theta.analysis.algorithm.ARG;
import hu.bme.mit.theta.analysis.algorithm.ArgNode;
import hu.bme.mit.theta.analysis.expr.ExprAction;
import hu.bme.mit.theta.analysis.expr.ExprState;

/**
 * Functional interface for pruning a node from an ARG.
 */
public interface NodePruner<S extends ExprState, A extends ExprAction> {

	/**
	 * Prunes the given node or one of its ancestors in the ARG from the given ARG.
	 *
	 * @param arg  the ARG
	 * @param node the node which or whose ancestor will be pruned from the ARG
	 */
	void prune(final ARG<S, A> arg, ArgNode<S, A> node);
}
