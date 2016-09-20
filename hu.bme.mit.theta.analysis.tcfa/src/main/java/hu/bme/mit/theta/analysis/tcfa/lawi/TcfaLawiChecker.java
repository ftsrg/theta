package hu.bme.mit.theta.analysis.tcfa.lawi;

import java.util.Optional;
import java.util.function.Predicate;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.Analysis;
import hu.bme.mit.theta.analysis.Precision;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.algorithm.impl.ARG;
import hu.bme.mit.theta.analysis.algorithm.impl.ArgNode;

public final class TcfaLawiChecker {

	public static <S extends State, A extends Action, P extends Precision> ARG<?, ?, ?> unwind(
			final Analysis<S, A, P> analysis, final Predicate<? super S> target, final P precision) {

		final ARG<S, A, P> arg = new ARG<>(analysis, target, precision);

		while (true) {
			final Optional<ArgNode<S, A>> optV = arg.getLeafNodes().stream().filter(v -> !v.isCovered()).findAny();

			if (optV.isPresent()) {
				final ArgNode<S, A> v = optV.get();

				v.foreachProperAncestors(w -> arg.close(w));
				dfs(arg, v, precision);

			} else {
				break;
			}
		}

		return arg;
	}

	private static <S extends State, A extends Action, P extends Precision> void dfs(final ARG<S, A, P> arg,
			final ArgNode<S, A> v, final P precision) {

		arg.close(v);

		if (!v.isCovered()) {

			if (v.isTarget()) {
				// refine(arg, v);
				v.foreachAncestors(w -> arg.close(w));
			}

			arg.expand(v, precision);
			v.foreachChildren(w -> dfs(arg, w, precision));
		}
	}

}