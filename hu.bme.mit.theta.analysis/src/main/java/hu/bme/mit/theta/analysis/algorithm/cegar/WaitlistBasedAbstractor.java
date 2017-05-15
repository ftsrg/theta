package hu.bme.mit.theta.analysis.algorithm.cegar;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;
import java.util.Optional;
import java.util.function.Function;
import java.util.function.Supplier;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.algorithm.ARG;
import hu.bme.mit.theta.analysis.algorithm.ArgBuilder;
import hu.bme.mit.theta.analysis.algorithm.ArgNode;
import hu.bme.mit.theta.analysis.reachedset.Partition;
import hu.bme.mit.theta.analysis.waitlist.Waitlist;
import hu.bme.mit.theta.common.ObjectUtils;
import hu.bme.mit.theta.common.logging.Logger;
import hu.bme.mit.theta.common.logging.impl.NullLogger;

/**
 * A waitlist-based implementation for the abstractor.
 */
public final class WaitlistBasedAbstractor<S extends State, A extends Action, P extends Prec>
		implements Abstractor<S, A, P> {

	private final ArgBuilder<S, A, P> argBuilder;
	private final Function<? super S, ?> projection;
	private final Supplier<? extends Waitlist<ArgNode<S, A>>> waitlistSupplier;
	private final Logger logger;

	private WaitlistBasedAbstractor(final ArgBuilder<S, A, P> argBuilder, final Function<? super S, ?> projection,
			final Supplier<? extends Waitlist<ArgNode<S, A>>> waitlistSupplier, final Logger logger) {
		this.argBuilder = checkNotNull(argBuilder);
		this.projection = checkNotNull(projection);
		this.waitlistSupplier = checkNotNull(waitlistSupplier);
		this.logger = checkNotNull(logger);
	}

	public static <S extends State, A extends Action, P extends Prec> WaitlistBasedAbstractor<S, A, P> create(
			final ArgBuilder<S, A, P> argBuilder, final Function<? super S, ?> projection,
			final Supplier<? extends Waitlist<ArgNode<S, A>>> waitlistSupplier, final Logger logger) {
		return new WaitlistBasedAbstractor<>(argBuilder, projection, waitlistSupplier, logger);
	}

	public static <S extends State, A extends Action, P extends Prec> WaitlistBasedAbstractor<S, A, P> create(
			final ArgBuilder<S, A, P> argBuilder, final Supplier<? extends Waitlist<ArgNode<S, A>>> waitlistSupplier,
			final Logger logger) {
		return new WaitlistBasedAbstractor<>(argBuilder, s -> 0, waitlistSupplier, logger);
	}

	public static <S extends State, A extends Action, P extends Prec> WaitlistBasedAbstractor<S, A, P> create(
			final ArgBuilder<S, A, P> argBuilder, final Function<? super S, ?> projection,
			final Supplier<? extends Waitlist<ArgNode<S, A>>> waitlistSupplier) {
		return new WaitlistBasedAbstractor<>(argBuilder, projection, waitlistSupplier, NullLogger.getInstance());
	}

	@Override
	public ARG<S, A> createArg() {
		return argBuilder.createArg();
	}

	@Override
	public AbstractorResult check(final ARG<S, A> arg, final P prec) {
		checkNotNull(arg);
		checkNotNull(prec);
		logger.writeln("Precision: ", prec, 3, 2);

		if (!arg.isInitialized()) {
			logger.write("(Re)initializing ARG...", 3, 2);
			argBuilder.init(arg, prec);
			logger.writeln("done.", 3);
		}

		logger.writeln(String.format("Starting ARG: %d nodes, %d incomplete, %d unsafe", arg.getNodes().count(),
				arg.getIncompleteNodes().count(), arg.getUnsafeNodes().count()), 3, 2);
		logger.write("Building ARG...", 3, 2);

		final Optional<ArgNode<S, A>> unsafeNode = searchForUnsafeNode(arg, prec);

		logger.writeln(String.format("done: %d nodes, %d incomplete, %d unsafe", arg.getNodes().count(),
				arg.getIncompleteNodes().count(), arg.getUnsafeNodes().count()), 3);

		if (unsafeNode.isPresent()) {
			assert !arg.isSafe() : "Returning safe ARG as unsafe";
			return AbstractorResult.unsafe();
		} else {
			assert arg.isSafe() : "Returning unsafe ARG as safe";
			assert arg.isComplete() : "Returning incomplete ARG as safe";
			return AbstractorResult.safe();
		}
	}

	private Optional<ArgNode<S, A>> searchForUnsafeNode(final ARG<S, A> arg, final P prec) {
		final Partition<ArgNode<S, A>, ?> reachedSet = Partition.of(n -> projection.apply(n.getState()));
		final Waitlist<ArgNode<S, A>> waitlist = waitlistSupplier.get();

		reachedSet.addAll(arg.getNodes());
		waitlist.addAll(arg.getIncompleteNodes());

		while (!waitlist.isEmpty()) {
			final ArgNode<S, A> node = waitlist.remove();

			close(node, reachedSet.get(node));
			if (!node.isCovered()) {
				if (node.isTarget()) {
					assert !node.isSafe() : "Safe node returned as unsafe";
					return Optional.of(node);
				} else {
					final Collection<ArgNode<S, A>> newNodes = argBuilder.expand(node, prec);
					reachedSet.addAll(newNodes);
					waitlist.addAll(newNodes);
				}
			}
		}
		return Optional.empty();
	}

	private void close(final ArgNode<S, A> node, final Collection<ArgNode<S, A>> candidates) {
		if (!node.isLeaf())
			return;
		for (final ArgNode<S, A> candidate : candidates) {
			if (candidate.mayCover(node)) {
				node.cover(candidate);
				return;
			}
		}
	}

	@Override
	public String toString() {
		return ObjectUtils.toStringBuilder(getClass().getSimpleName()).add(waitlistSupplier.get()).toString();
	}

}
