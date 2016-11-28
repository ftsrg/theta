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
import hu.bme.mit.theta.common.logging.Logger;
import hu.bme.mit.theta.common.logging.impl.NullLogger;
import hu.bme.mit.theta.common.waitlist.Waitlist;

public final class WaitlistBasedAbstractor<S extends State, A extends Action, P extends Precision>
		implements Abstractor<S, A, P> {

	private final ArgBuilder<S, A, P> argBuilder;
	private final Analysis<S, ? super A, ? super P> analysis;
	private final Supplier<? extends Waitlist<ArgNode<S, A>>> waitlistSupplier;
	private final Logger logger;

	private WaitlistBasedAbstractor(final LTS<? super S, ? extends A> lts,
			final Analysis<S, ? super A, ? super P> analysis, final Predicate<? super S> target,
			final Supplier<? extends Waitlist<ArgNode<S, A>>> waitlistSupplier, final Logger logger) {
		this.analysis = checkNotNull(analysis);
		checkNotNull(lts);
		checkNotNull(target);
		argBuilder = ArgBuilder.create(lts, analysis, target);
		this.waitlistSupplier = checkNotNull(waitlistSupplier);
		this.logger = checkNotNull(logger);
	}

	public static <S extends State, A extends Action, P extends Precision> WaitlistBasedAbstractor<S, A, P> create(
			final LTS<? super S, ? extends A> lts, final Analysis<S, ? super A, ? super P> analysis,
			final Predicate<? super S> target, final Supplier<? extends Waitlist<ArgNode<S, A>>> waitlistSupplier,
			final Logger logger) {
		return new WaitlistBasedAbstractor<>(lts, analysis, target, waitlistSupplier, logger);
	}

	public static <S extends State, A extends Action, P extends Precision> WaitlistBasedAbstractor<S, A, P> create(
			final LTS<? super S, ? extends A> lts, final Analysis<S, ? super A, ? super P> analysis,
			final Predicate<? super S> target, final Supplier<? extends Waitlist<ArgNode<S, A>>> waitlistSupplier) {
		return new WaitlistBasedAbstractor<>(lts, analysis, target, waitlistSupplier, NullLogger.getInstance());
	}

	@Override
	public ARG<S, A> createArg() {
		return ARG.create(analysis.getDomain());
	}

	@Override
	public AbstractorResult check(final ARG<S, A> arg, final P precision) {
		checkNotNull(arg);
		checkNotNull(precision);
		logger.write("Precision: ", 3, 2).writeln(precision, 3);

		if (!arg.isInitialized()) {
			logger.write("(Re)initializing ARG...", 3, 2);
			argBuilder.init(arg, precision);
			logger.writeln("done.", 3);
		}

		logger.write(arg.getNodes().count(), 3, 2).write(" node(s), ", 3).write(arg.getIncompleteNodes().count(), 3)
				.write(" incomplete, ", 3).write(arg.getUnsafeNodes().count(), 3).write(" unsafe", 3).writeln(3);

		if (arg.getUnsafeNodes().findAny().isPresent()) {
			return AbstractorResult.unsafe();
		}

		ArgNode<S, A> unsafeNode = null;

		final Waitlist<ArgNode<S, A>> waitlist = waitlistSupplier.get();
		waitlist.addAll(arg.getIncompleteNodes());

		while (!waitlist.isEmpty() && unsafeNode == null) {
			final ArgNode<S, A> node = waitlist.remove();

			if (!node.isSafe(analysis.getDomain())) {
				unsafeNode = node;
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

		logger.write("ARG finished: ", 3, 2).write(arg.getNodes().count(), 3).write(" node(s), ", 3)
				.write(arg.getIncompleteNodes().count(), 3).write(" incomplete, ", 3)
				.write(arg.getUnsafeNodes().count(), 3).write(" unsafe", 3).writeln(3);

		if (unsafeNode == null) {
			return AbstractorResult.safe();
		} else {
			return AbstractorResult.unsafe();
		}
	}

}
