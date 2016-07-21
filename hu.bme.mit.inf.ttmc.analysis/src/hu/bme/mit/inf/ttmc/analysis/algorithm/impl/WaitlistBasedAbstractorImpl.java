package hu.bme.mit.inf.ttmc.analysis.algorithm.impl;

import static com.google.common.base.Preconditions.checkNotNull;
import static com.google.common.base.Preconditions.checkState;

import hu.bme.mit.inf.ttmc.analysis.Action;
import hu.bme.mit.inf.ttmc.analysis.ActionFunction;
import hu.bme.mit.inf.ttmc.analysis.Domain;
import hu.bme.mit.inf.ttmc.analysis.InitFunction;
import hu.bme.mit.inf.ttmc.analysis.Precision;
import hu.bme.mit.inf.ttmc.analysis.State;
import hu.bme.mit.inf.ttmc.analysis.TargetPredicate;
import hu.bme.mit.inf.ttmc.analysis.TransferFunction;
import hu.bme.mit.inf.ttmc.analysis.algorithm.Abstractor;
import hu.bme.mit.inf.ttmc.analysis.algorithm.AbstractorStatus;
import hu.bme.mit.inf.ttmc.analysis.algorithm.impl.waitlist.Waitlist;

public class WaitlistBasedAbstractorImpl<S extends State, A extends Action, P extends Precision>
		implements Abstractor<S, A, P> {

	private final ARGBuilder<S, A> builder;

	private final InitFunction<S, P> initFunction;
	private final TransferFunction<S, A, P> transferFunction;

	private ARG<S, A> arg;

	private final Waitlist<ARGNode<S, A>> waitlist;

	public WaitlistBasedAbstractorImpl(final Domain<S> domain,
			final ActionFunction<? super S, ? extends A> actionFunction, final InitFunction<S, P> initFunction,
			final TransferFunction<S, A, P> transferFunction, final TargetPredicate<? super S> targetPredicate,
			final Waitlist<ARGNode<S, A>> waitlist) {
		checkNotNull(domain);
		checkNotNull(actionFunction);
		checkNotNull(targetPredicate);
		this.initFunction = checkNotNull(initFunction);
		this.transferFunction = checkNotNull(transferFunction);
		this.waitlist = checkNotNull(waitlist);
		builder = new ARGBuilder<>(domain, actionFunction, targetPredicate);
	}

	@Override
	public ARG<S, A> getARG() {
		checkState(arg != null);
		return arg;
	}

	@Override
	public void init(final P precision) {
		arg = builder.create(initFunction, precision);
		waitlist.clear();
	}

	@Override
	public AbstractorStatus check(final P precision) {
		waitlist.addAll(arg.getNodes());

		while (!waitlist.isEmpty()) {
			final ARGNode<S, A> node = waitlist.remove();
			arg.close(node);
			if (!node.isCovered() && !node.isTarget() && !node.isExpanded()) {
				builder.expand(arg, node, transferFunction, precision);
				for (final ARGEdge<S, A> outEdge : node.getOutEdges()) {
					final ARGNode<S, A> succNode = outEdge.getTarget();
					if (!succNode.isTarget()) {
						waitlist.add(succNode);
					}
				}
			}
		}

		return getStatus();
	}

	@Override
	public AbstractorStatus getStatus() {
		checkState(arg != null);
		return arg.getTargetNodes().size() == 0 ? AbstractorStatus.OK : AbstractorStatus.COUNTEREXAMPLE;
	}

}
