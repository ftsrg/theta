package hu.bme.mit.theta.xcfa.analysis.impl.interleavings.por;

import hu.bme.mit.theta.analysis.algorithm.ARG;
import hu.bme.mit.theta.analysis.algorithm.ArgEdge;
import hu.bme.mit.theta.analysis.algorithm.ArgNode;
import hu.bme.mit.theta.analysis.expr.refinement.NodePruner;
import hu.bme.mit.theta.xcfa.analysis.impl.interleavings.XcfaAction;
import hu.bme.mit.theta.xcfa.analysis.impl.interleavings.XcfaState;
import hu.bme.mit.theta.xcfa.model.XcfaLocation;
import hu.bme.mit.theta.xcfa.model.utils.XcfaUtils;

import java.util.List;

/**
 * Prunes the given node from the given ARG if the action of its incoming edge is not part of an atomic block.
 * Otherwise, the closest ancestor of the node is pruned for whom the above condition holds.
 *
 * @param <S> {@link XcfaState}
 * @param <A> {@link XcfaAction}
 */
public class AtomicNodePruner<S extends XcfaState<?>, A extends XcfaAction> implements NodePruner<S, A> {
	@Override
	public void prune(final ARG<S, A> arg, ArgNode<S, A> node) {
		XcfaLocation currentLoc = node.getState().getCurrentLoc();
		List<XcfaLocation> atomicLocations = XcfaUtils.getAtomicBlockInnerLocations(currentLoc.getParent());
		while (node.getInEdge().isPresent()) {
			ArgEdge<S, A> inEdge = node.getInEdge().get();
			ArgNode<S, A> previousNode = inEdge.getSource();
			Integer process = inEdge.getAction().getProcess();
			if (!atomicLocations.contains(previousNode.getState().getProcessLocs().get(process))) {
				break;
			}
			node = inEdge.getSource();
		}
		arg.prune(node);
	}
}
