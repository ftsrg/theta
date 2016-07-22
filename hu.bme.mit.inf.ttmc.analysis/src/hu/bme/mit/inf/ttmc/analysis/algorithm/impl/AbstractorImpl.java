package hu.bme.mit.inf.ttmc.analysis.algorithm.impl;

import static com.google.common.base.Preconditions.checkNotNull;
import static com.google.common.base.Preconditions.checkState;

import java.util.ArrayList;
import java.util.Collection;

import hu.bme.mit.inf.ttmc.analysis.Action;
import hu.bme.mit.inf.ttmc.analysis.ActionFunction;
import hu.bme.mit.inf.ttmc.analysis.Analysis;
import hu.bme.mit.inf.ttmc.analysis.InitFunction;
import hu.bme.mit.inf.ttmc.analysis.Precision;
import hu.bme.mit.inf.ttmc.analysis.State;
import hu.bme.mit.inf.ttmc.analysis.TargetPredicate;
import hu.bme.mit.inf.ttmc.analysis.TransferFunction;
import hu.bme.mit.inf.ttmc.analysis.algorithm.Abstractor;
import hu.bme.mit.inf.ttmc.analysis.algorithm.AbstractorStatus;

public class AbstractorImpl<S extends State, A extends Action, P extends Precision> implements Abstractor<S, A, P> {

	private final ARGBuilder<S, A> builder;

	private final InitFunction<S, P> initFunction;
	private final TransferFunction<S, A, P> transferFunction;

	private ARG<S, A> arg;

	public AbstractorImpl(final Analysis<S, A, P> analysis, final ActionFunction<? super S, ? extends A> actionFunction,
			final TargetPredicate<? super S> targetPredicate) {
		checkNotNull(analysis);
		checkNotNull(actionFunction);
		checkNotNull(targetPredicate);
		initFunction = analysis.getInitFunction();
		transferFunction = analysis.getTransferFunction();
		builder = new ARGBuilder<>(analysis.getDomain(), actionFunction, targetPredicate);
	}

	@Override
	public ARG<S, A> getARG() {
		checkState(arg != null);
		return arg;
	}

	@Override
	public void init(final P precision) {
		arg = builder.create(initFunction, precision);
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
			builder.expand(arg, node, transferFunction, precision);
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
