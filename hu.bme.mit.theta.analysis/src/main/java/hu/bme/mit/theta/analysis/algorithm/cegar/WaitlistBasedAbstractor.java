package hu.bme.mit.theta.analysis.algorithm.cegar;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.function.Predicate;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.Analysis;
import hu.bme.mit.theta.analysis.Precision;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.algorithm.ARG;
import hu.bme.mit.theta.analysis.algorithm.ArgBuilder;
import hu.bme.mit.theta.analysis.algorithm.ArgNode;
import hu.bme.mit.theta.common.waitlist.Waitlist;

public class WaitlistBasedAbstractor<S extends State, A extends Action, P extends Precision>
		implements Abstractor<S, A, P> {

	private final Waitlist<ArgNode<S, A>> waitlist;
	private final ArgBuilder<S, A, P> argBuilder;
	private final Analysis<S, A, P> analysis;

	private WaitlistBasedAbstractor(final Analysis<S, A, P> analysis, final Predicate<? super S> target,
			final Waitlist<ArgNode<S, A>> waitlist) {
		this.analysis = checkNotNull(analysis);
		checkNotNull(target);
		this.waitlist = checkNotNull(waitlist);
		argBuilder = ArgBuilder.create(analysis, target);
	}

	public static <S extends State, A extends Action, P extends Precision> WaitlistBasedAbstractor<S, A, P> create(
			final Analysis<S, A, P> analysis, final Predicate<? super S> target,
			final Waitlist<ArgNode<S, A>> waitlist) {
		return new WaitlistBasedAbstractor<>(analysis, target, waitlist);
	}

	@Override
	public ARG<S, A> init(final P precision) {
		final ARG<S, A> arg = ARG.create(analysis.getDomain());
		argBuilder.init(arg, precision);
		return arg;
	}

	@Override
	public AbstractorStatus<S, A> check(final ARG<S, A> arg, final P precision) {
		checkNotNull(arg);
		checkNotNull(precision);

		waitlist.clear();
		waitlist.addAll(arg.getLeafNodes());
		while (!waitlist.isEmpty()) {
			final ArgNode<S, A> node = waitlist.remove();

			if (node.isTarget()) {
				waitlist.clear();
				return AbstractorStatus.create(arg);
			}

			argBuilder.close(node);
			if (!node.isCovered()) {
				argBuilder.expand(node, precision);
				waitlist.addAll(node.getSuccNodes());
			}
		}

		waitlist.clear();
		return AbstractorStatus.create(arg);
	}

}
