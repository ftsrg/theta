package hu.bme.mit.theta.analysis.algorithm;

import java.util.Comparator;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.State;

public class ArgNodeComparators {

	private ArgNodeComparators() {
	}

	////

	public static <S extends State, A extends Action> Comparator<ArgNode<S, A>> invert(
			final Comparator<ArgNode<S, A>> comparator) {
		return new Inverter<>(comparator);
	}

	public static <S extends State, A extends Action> Comparator<ArgNode<S, A>> bfs() {
		return new DepthOrder<>();
	}

	public static <S extends State, A extends Action> Comparator<ArgNode<S, A>> dfs() {
		return invert(bfs());
	}

	public static <S extends State, A extends Action> Comparator<ArgNode<S, A>> creationAsc() {
		return new CreationOrder<>();
	}

	public static <S extends State, A extends Action> Comparator<ArgNode<S, A>> creationDesc() {
		return invert(creationAsc());
	}

	////

	private static final class DepthOrder<S extends State, A extends Action> implements Comparator<ArgNode<S, A>> {
		@Override
		public int compare(final ArgNode<S, A> n1, final ArgNode<S, A> n2) {
			return Integer.compare(n1.getDepth(), n2.getDepth());
		}
	}

	private static final class CreationOrder<S extends State, A extends Action> implements Comparator<ArgNode<S, A>> {
		@Override
		public int compare(final ArgNode<S, A> n1, final ArgNode<S, A> n2) {
			return Integer.compare(n1.getId(), n2.getId());
		}
	}

	private static final class Inverter<S extends State, A extends Action> implements Comparator<ArgNode<S, A>> {
		private final Comparator<ArgNode<S, A>> comparator;

		private Inverter(final Comparator<ArgNode<S, A>> comparator) {
			this.comparator = comparator;
		}

		@Override
		public int compare(final ArgNode<S, A> n1, final ArgNode<S, A> n2) {
			return comparator.compare(n1, n2) * -1;
		}
	}
}
