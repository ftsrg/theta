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
import hu.bme.mit.theta.common.waitlist.FifoWaitlist;
import hu.bme.mit.theta.common.waitlist.Waitlist;

public class WaitlistBasedAbstractor<S extends State, A extends Action, P extends Precision>
		implements Abstractor<S, A, P> {

	private final ArgBuilder<S, A, ? super P> argBuilder;
	private final Analysis<S, A, ? super P> analysis;

	private WaitlistBasedAbstractor(final Analysis<S, A, ? super P> analysis, final Predicate<? super S> target) {
		this.analysis = checkNotNull(analysis);
		checkNotNull(target);
		argBuilder = ArgBuilder.create(analysis, target);
	}

	public static <S extends State, A extends Action, P extends Precision> WaitlistBasedAbstractor<S, A, P> create(
			final Analysis<S, A, ? super P> analysis, final Predicate<? super S> target) {
		return new WaitlistBasedAbstractor<>(analysis, target);
	}

	@Override
	public AbstractionState<S, A, P> init(final P precision) {
		final ARG<S, A> arg = ARG.create(analysis.getDomain());
		argBuilder.init(arg, precision);
		// TODO: parameterize the type of waitlist created
		final FifoWaitlist<ArgNode<S, A>> waitlist = new FifoWaitlist<>();
		waitlist.addAll(arg.getInitNodes());
		return AbstractionState.create(arg, waitlist, precision);
	}

	@Override
	public AbstractorStatus<S, A, P> check(final AbstractionState<S, A, P> abstractionState) {
		checkNotNull(abstractionState);

		final ARG<S, A> arg = abstractionState.getArg();
		final Waitlist<ArgNode<S, A>> waitlist = abstractionState.getWaitlist();
		final P precision = abstractionState.getPrecision();

		while (!waitlist.isEmpty()) {
			final ArgNode<S, A> node = waitlist.remove();

			if (node.isTarget()) {
				return AbstractorStatus.create(AbstractionState.create(arg, waitlist, precision));
			}

			argBuilder.close(node);
			if (!node.isCovered()) {
				argBuilder.expand(node, precision);
				waitlist.addAll(node.getSuccNodes());
			}
		}

		return AbstractorStatus.create(AbstractionState.create(arg, waitlist, precision));
	}

}
