package hu.bme.mit.theta.analysis.algorithm.cegar;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Optional;
import java.util.function.Supplier;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.Precision;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.algorithm.ARG;
import hu.bme.mit.theta.analysis.algorithm.ArgBuilder;
import hu.bme.mit.theta.analysis.algorithm.ArgNode;
import hu.bme.mit.theta.analysis.waitlist.Waitlist;
import hu.bme.mit.theta.common.ObjectUtils;
import hu.bme.mit.theta.common.logging.Logger;
import hu.bme.mit.theta.common.logging.impl.NullLogger;

public final class WaitlistBasedAbstractor<S extends State, A extends Action, P extends Precision>
		implements Abstractor<S, A, P> {

	private final ArgBuilder<S, A, P> argBuilder;
	private final Supplier<? extends Waitlist<ArgNode<S, A>>> waitlistSupplier;
	private final Logger logger;

	private WaitlistBasedAbstractor(final ArgBuilder<S, A, P> argBuilder,
			final Supplier<? extends Waitlist<ArgNode<S, A>>> waitlistSupplier, final Logger logger) {
		this.argBuilder = checkNotNull(argBuilder);
		this.waitlistSupplier = checkNotNull(waitlistSupplier);
		this.logger = checkNotNull(logger);
	}

	public static <S extends State, A extends Action, P extends Precision> WaitlistBasedAbstractor<S, A, P> create(
			final ArgBuilder<S, A, P> argBuilder, final Supplier<? extends Waitlist<ArgNode<S, A>>> waitlistSupplier,
			final Logger logger) {
		return new WaitlistBasedAbstractor<>(argBuilder, waitlistSupplier, logger);
	}

	public static <S extends State, A extends Action, P extends Precision> WaitlistBasedAbstractor<S, A, P> create(
			final ArgBuilder<S, A, P> argBuilder, final Supplier<? extends Waitlist<ArgNode<S, A>>> waitlistSupplier) {
		return new WaitlistBasedAbstractor<>(argBuilder, waitlistSupplier, NullLogger.getInstance());
	}

	@Override
	public ARG<S, A> createArg() {
		return argBuilder.createArg();
	}

	@Override
	public AbstractorResult check(final ARG<S, A> arg, final P precision) {
		checkNotNull(arg);
		checkNotNull(precision);
		logger.writeln("Precision: ", precision, 3, 2);

		if (!arg.isInitialized()) {
			logger.write("(Re)initializing ARG...", 3, 2);
			argBuilder.init(arg, precision);
			logger.writeln("done.", 3);
		}

		logger.writeln(String.format("Starting ARG: %d nodes, %d incomplete, %d unsafe", arg.getNodes().count(),
				arg.getIncompleteNodes().count(), arg.getUnsafeNodes().count()), 3, 2);

		final Optional<ArgNode<S, A>> unsafeNode = searchForUnsafeNode(arg, precision);

		logger.writeln(String.format("done: %d nodes, %d incomplete, %d unsafe", arg.getNodes().count(),
				arg.getIncompleteNodes().count(), arg.getUnsafeNodes().count()), 3);

		if (unsafeNode.isPresent()) {
			return AbstractorResult.unsafe();
		} else {
			return AbstractorResult.safe();
		}
	}

	private Optional<ArgNode<S, A>> searchForUnsafeNode(final ARG<S, A> arg, final P precision) {
		final Optional<ArgNode<S, A>> unsafeNode = arg.getUnsafeNodes().findAny();
		if (unsafeNode.isPresent()) {
			return unsafeNode;
		}

		final Waitlist<ArgNode<S, A>> waitlist = waitlistSupplier.get();
		waitlist.addAll(arg.getIncompleteNodes());

		logger.write("Building ARG...", 3, 2);

		while (!waitlist.isEmpty()) {
			final ArgNode<S, A> node = waitlist.remove();

			argBuilder.close(node);
			if (!node.isExcluded()) {
				if (node.isTarget()) {
					return Optional.of(node);
				} else {
					argBuilder.expand(node, precision);
					waitlist.addAll(node.getSuccNodes());
				}
			}
		}
		return Optional.empty();
	}

	@Override
	public String toString() {
		return ObjectUtils.toStringBuilder(getClass().getSimpleName()).add(waitlistSupplier.get()).toString();
	}

}
