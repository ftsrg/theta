package hu.bme.mit.theta.analysis.algorithm.cegar;

import static com.google.common.base.Preconditions.checkNotNull;
import static com.google.common.base.Preconditions.checkState;

import java.util.function.Predicate;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.Analysis;
import hu.bme.mit.theta.analysis.Precision;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.algorithm.ARG;
import hu.bme.mit.theta.analysis.algorithm.ArgBuilder;
import hu.bme.mit.theta.analysis.algorithm.ArgEdge;
import hu.bme.mit.theta.analysis.algorithm.ArgNode;
import hu.bme.mit.theta.analysis.algorithm.Waitlist;

public class WaitlistBasedAbstractor<S extends State, A extends Action, P extends Precision>
		implements Abstractor<S, A, P> {

	private final Waitlist<ArgNode<S, A>> waitlist;
	private final ArgBuilder<S, A, P> argBuilder;

	private ARG<S, A> arg;

	public WaitlistBasedAbstractor(final Analysis<S, A, P> analysis, final Predicate<? super S> target,
			final Waitlist<ArgNode<S, A>> waitlist) {
		checkNotNull(analysis);
		checkNotNull(target);
		this.waitlist = checkNotNull(waitlist);
		argBuilder = ArgBuilder.create(analysis, target);
	}

	@Override
	public ARG<S, A> getARG() {
		checkState(arg != null);
		return arg;
	}

	@Override
	public void init(final P precision) {
		arg = argBuilder.createArg(precision);
		waitlist.clear();
	}

	@Override
	public void check(final P precision) {
		checkState(arg != null);

		waitlist.addAll(arg.getNodes());
		while (!waitlist.isEmpty()) {
			final ArgNode<S, A> node = waitlist.remove();

			if (node.isTarget()) {
				return;
			}

			argBuilder.tryToClose(node);
			if (!node.isCovered()) {
				expand(precision, node);
			}
		}
	}

	private void expand(final P precision, final ArgNode<S, A> node) {
		argBuilder.expandNode(node, precision);
		for (final ArgEdge<S, A> outEdge : node.getOutEdges()) {
			final ArgNode<S, A> succNode = outEdge.getTarget();
			if (!succNode.isTarget()) {
				waitlist.add(succNode);
			}
		}
	}

	@Override
	public AbstractorStatus getStatus() {
		checkState(arg != null);
		return arg.getTargetNodes().size() == 0 ? AbstractorStatus.OK : AbstractorStatus.COUNTEREXAMPLE;
	}

}
