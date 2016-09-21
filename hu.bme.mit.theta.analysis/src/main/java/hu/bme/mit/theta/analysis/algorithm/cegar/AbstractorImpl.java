package hu.bme.mit.theta.analysis.algorithm.cegar;

import static com.google.common.base.Preconditions.checkNotNull;
import static com.google.common.base.Preconditions.checkState;

import java.util.ArrayList;
import java.util.Collection;
import java.util.function.Predicate;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.Analysis;
import hu.bme.mit.theta.analysis.Precision;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.algorithm.ARG;
import hu.bme.mit.theta.analysis.algorithm.ArgEdge;
import hu.bme.mit.theta.analysis.algorithm.ArgNode;

public class AbstractorImpl<S extends State, A extends Action, P extends Precision> implements Abstractor<S, A, P> {

	private final Analysis<S, A, P> analysis;
	private final Predicate<? super S> target;

	private ARG<S, A, P> arg;

	public AbstractorImpl(final Analysis<S, A, P> analysis, final Predicate<? super S> target) {
		this.analysis = checkNotNull(analysis);
		this.target = checkNotNull(target);
	}

	@Override
	public ARG<S, A, P> getARG() {
		checkState(arg != null);
		return arg;
	}

	@Override
	public void init(final P precision) {
		arg = new ARG<>(analysis, target, precision);
	}

	@Override
	public void check(final P precision) {
		final Collection<ArgNode<S, A>> nodes = new ArrayList<>(arg.getNodes());
		for (final ArgNode<S, A> node : nodes) {
			if (!node.isTarget() && !node.isExpanded() && !node.isCovered()) {
				dfs(node, precision);
			}
		}
	}

	private void dfs(final ArgNode<S, A> node, final P precision) {
		arg.close(node);
		if (!node.isCovered()) {
			arg.expand(node, precision);
			for (final ArgEdge<S, A> outEdge : node.getOutEdges()) {
				final ArgNode<S, A> succNode = outEdge.getTarget();
				if (!succNode.isTarget()) {
					dfs(succNode, precision);
				}
			}
		}
	}

	@Override
	public AbstractorStatus getStatus() {
		checkState(arg != null);
		return arg.getTargetNodes().size() == 0 ? AbstractorStatus.OK : AbstractorStatus.COUNTEREXAMPLE;
	}

}
