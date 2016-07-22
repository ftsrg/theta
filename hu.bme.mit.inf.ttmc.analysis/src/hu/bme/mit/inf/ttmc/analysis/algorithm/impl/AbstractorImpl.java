package hu.bme.mit.inf.ttmc.analysis.algorithm.impl;

import static com.google.common.base.Preconditions.checkNotNull;
import static com.google.common.base.Preconditions.checkState;

import java.util.ArrayList;
import java.util.Collection;
import java.util.function.Predicate;

import hu.bme.mit.inf.ttmc.analysis.Action;
import hu.bme.mit.inf.ttmc.analysis.Analysis;
import hu.bme.mit.inf.ttmc.analysis.Precision;
import hu.bme.mit.inf.ttmc.analysis.State;
import hu.bme.mit.inf.ttmc.analysis.algorithm.Abstractor;
import hu.bme.mit.inf.ttmc.analysis.algorithm.AbstractorStatus;

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
		final Collection<ARGNode<S, A>> nodes = new ArrayList<>(arg.getNodes());
		for (final ARGNode<S, A> node : nodes) {
			if (!node.isTarget() && !node.isExpanded() && !node.isCovered()) {
				dfs(node, precision);
			}
		}
	}

	private void dfs(final ARGNode<S, A> node, final P precision) {
		arg.close(node);
		if (!node.isCovered()) {
			arg.expand(node, precision);
			for (final ARGEdge<S, A> outEdge : node.getOutEdges()) {
				final ARGNode<S, A> succNode = outEdge.getTarget();
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
