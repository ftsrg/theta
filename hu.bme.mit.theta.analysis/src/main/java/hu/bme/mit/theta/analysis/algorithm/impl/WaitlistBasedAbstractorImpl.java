package hu.bme.mit.theta.analysis.algorithm.impl;

import static com.google.common.base.Preconditions.checkNotNull;
import static com.google.common.base.Preconditions.checkState;

import java.util.function.Predicate;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.Analysis;
import hu.bme.mit.theta.analysis.Precision;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.algorithm.Abstractor;
import hu.bme.mit.theta.analysis.algorithm.AbstractorStatus;
import hu.bme.mit.theta.analysis.algorithm.impl.waitlist.Waitlist;

public class WaitlistBasedAbstractorImpl<S extends State, A extends Action, P extends Precision>
		implements Abstractor<S, A, P> {

	private final Analysis<S, A, P> analysis;
	private final Predicate<? super S> target;

	private final Waitlist<ArgNode<S, A>> waitlist;

	private ARG<S, A, P> arg;

	public WaitlistBasedAbstractorImpl(final Analysis<S, A, P> analysis, final Predicate<? super S> target,
			final Waitlist<ArgNode<S, A>> waitlist) {
		this.analysis = checkNotNull(analysis);
		this.target = checkNotNull(target);
		this.waitlist = checkNotNull(waitlist);
	}

	@Override
	public ARG<S, A, P> getARG() {
		checkState(arg != null);
		return arg;
	}

	@Override
	public void init(final P precision) {
		arg = new ARG<>(analysis, target, precision);
		waitlist.clear();
	}

	@Override
	public void check(final P precision) {
		waitlist.addAll(arg.getNodes());

		while (!waitlist.isEmpty()) {
			final ArgNode<S, A> node = waitlist.remove();
			arg.close(node);
			if (!node.isCovered() && !node.isTarget() && !node.isExpanded()) {
				arg.expand(node, precision);
				for (final ArgEdge<S, A> outEdge : node.getOutEdges()) {
					final ArgNode<S, A> succNode = outEdge.getTarget();
					if (!succNode.isTarget()) {
						waitlist.add(succNode);
					}
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
