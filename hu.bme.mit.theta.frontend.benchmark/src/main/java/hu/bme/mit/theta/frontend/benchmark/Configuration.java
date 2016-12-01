package hu.bme.mit.theta.frontend.benchmark;

import java.util.Optional;
import java.util.concurrent.ExecutionException;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.Future;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.TimeoutException;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.Precision;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.algorithm.SafetyChecker;
import hu.bme.mit.theta.analysis.algorithm.SafetyStatus;

public class Configuration<S extends State, A extends Action, P extends Precision> {
	private final SafetyChecker<S, A, P> checker;
	private final P initPrecision;

	private Configuration(final SafetyChecker<S, A, P> checker, final P initPrecision) {
		this.checker = checker;
		this.initPrecision = initPrecision;
	}

	public static <S extends State, A extends Action, P extends Precision> Configuration<S, A, P> create(
			final SafetyChecker<S, A, P> checker, final P initPrecision) {
		return new Configuration<>(checker, initPrecision);
	}

	public SafetyStatus<S, A> check() throws InterruptedException {
		return checker.check(initPrecision);
	}

	public Optional<SafetyStatus<?, ?>> check(final long timeout, final TimeUnit unit) {
		final ExecutorService executor = Executors.newFixedThreadPool(1);
		final Future<SafetyStatus<S, A>> future = executor.submit(() -> {
			return checker.check(initPrecision);
		});

		try {
			final SafetyStatus<S, A> result = future.get(timeout, unit);
			return Optional.of(result);
		} catch (final InterruptedException | ExecutionException | TimeoutException e) {
			return Optional.empty();
		} finally {
			future.cancel(true);
			executor.shutdownNow();
		}

	}

}
