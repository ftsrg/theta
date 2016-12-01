package hu.bme.mit.theta.analysis.algorithm.cegar;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.function.Predicate;
import java.util.function.Supplier;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.Analysis;
import hu.bme.mit.theta.analysis.LTS;
import hu.bme.mit.theta.analysis.Precision;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.algorithm.ARG;
import hu.bme.mit.theta.analysis.algorithm.ArgBuilder;
import hu.bme.mit.theta.analysis.algorithm.ArgNode;
import hu.bme.mit.theta.common.waitlist.Waitlist;

public final class WaitlistBasedAbstractor<S extends State, A extends Action, P extends Precision>
		implements Abstractor<S, A, P> {

	private final ArgBuilder<S, A, P> argBuilder;
	private final Analysis<S, ? super A, ? super P> analysis;
	private final Supplier<? extends Waitlist<ArgNode<S, A>>> waitlistSupplier;

	private WaitlistBasedAbstractor(final LTS<? super S, ? extends A> lts,
			final Analysis<S, ? super A, ? super P> analysis, final Predicate<? super S> target,
			final Supplier<? extends Waitlist<ArgNode<S, A>>> waitlistSupplier) {
		this.analysis = checkNotNull(analysis);
		checkNotNull(lts);
		checkNotNull(target);
		argBuilder = ArgBuilder.create(lts, analysis, target);
		this.waitlistSupplier = checkNotNull(waitlistSupplier);
	}

	public static <S extends State, A extends Action, P extends Precision> WaitlistBasedAbstractor<S, A, P> create(
			final LTS<? super S, ? extends A> lts, final Analysis<S, ? super A, ? super P> analysis,
			final Predicate<? super S> target, final Supplier<? extends Waitlist<ArgNode<S, A>>> waitlistSupplier) {
		return new WaitlistBasedAbstractor<>(lts, analysis, target, waitlistSupplier);
	}

	@Override
	public ARG<S, A> createArg() {
		return ARG.create(analysis.getDomain());
	}

	@Override
	public AbstractorResult check(final ARG<S, A> arg, final P precision) {
		checkNotNull(arg);
		checkNotNull(precision);

		if (!arg.isInitialized()) {
			argBuilder.init(arg, precision);
		}

		if (arg.getUnsafeNodes().findAny().isPresent()) {
			return AbstractorResult.unsafe();
		}

		final Waitlist<ArgNode<S, A>> waitlist = waitlistSupplier.get();
		waitlist.addAll(arg.getIncompleteNodes());

		while (!waitlist.isEmpty()) {
			final ArgNode<S, A> node = waitlist.remove();

			if (!node.isSafe()) {
				return AbstractorResult.unsafe();
			}

			if (node.isTarget()) {
				continue;
			}
			argBuilder.close(node);

			if (node.isCovered()) {
				continue;
			}
			argBuilder.expand(node, precision);
			waitlist.addAll(node.getSuccNodes());
		}

		return AbstractorResult.safe();
	}

}
