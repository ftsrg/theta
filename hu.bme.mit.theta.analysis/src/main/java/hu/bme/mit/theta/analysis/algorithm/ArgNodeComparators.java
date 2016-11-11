package hu.bme.mit.theta.analysis.algorithm;

import java.util.Comparator;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.State;

public class ArgNodeComparators {

	private ArgNodeComparators() {
	}

	////

	public static Comparator<ArgNode<? extends State, ? extends Action>> creationAsc() {
		return new CreationOrder();
	}

	public static Comparator<ArgNode<? extends State, ? extends Action>> creationDesc() {
		return invert(creationAsc());
	}

	public static Comparator<ArgNode<? extends State, ? extends Action>> invert(
			final Comparator<ArgNode<? extends State, ? extends Action>> comparator) {
		return new Inverter(comparator);
	}

	public static Comparator<ArgNode<? extends State, ? extends Action>> combine(
			final Comparator<ArgNode<? extends State, ? extends Action>> first,
			final Comparator<ArgNode<? extends State, ? extends Action>> then) {
		return new Combinator(first, then);
	}

	public static Comparator<ArgNode<? extends State, ? extends Action>> bfs() {
		return combine(new DepthOrder(), new CreationOrder());
	}

	public static Comparator<ArgNode<? extends State, ? extends Action>> dfs() {
		return combine(invert(new DepthOrder()), new CreationOrder());
	}

	public static Comparator<ArgNode<? extends State, ? extends Action>> targetFirst() {
		return new TargetFirst();
	}

	////

	private static final class DepthOrder implements Comparator<ArgNode<? extends State, ? extends Action>> {
		@Override
		public int compare(final ArgNode<? extends State, ? extends Action> n1,
				final ArgNode<? extends State, ? extends Action> n2) {
			return Integer.compare(n1.getDepth(), n2.getDepth());
		}
	}

	private static final class CreationOrder implements Comparator<ArgNode<? extends State, ? extends Action>> {
		@Override
		public int compare(final ArgNode<? extends State, ? extends Action> n1,
				final ArgNode<? extends State, ? extends Action> n2) {
			return Integer.compare(n1.getId(), n2.getId());
		}
	}

	private static final class TargetFirst implements Comparator<ArgNode<? extends State, ? extends Action>> {
		@Override
		public int compare(final ArgNode<? extends State, ? extends Action> n1,
				final ArgNode<? extends State, ? extends Action> n2) {
			return Boolean.compare(n1.isTarget(), n2.isTarget()) * -1;
		}
	}

	private static final class Inverter implements Comparator<ArgNode<? extends State, ? extends Action>> {
		private final Comparator<ArgNode<? extends State, ? extends Action>> comparator;

		private Inverter(final Comparator<ArgNode<? extends State, ? extends Action>> comparator) {
			this.comparator = comparator;
		}

		@Override
		public int compare(final ArgNode<? extends State, ? extends Action> n1,
				final ArgNode<? extends State, ? extends Action> n2) {
			return comparator.compare(n1, n2) * -1;
		}
	}

	private static final class Combinator implements Comparator<ArgNode<? extends State, ? extends Action>> {
		private final Comparator<ArgNode<? extends State, ? extends Action>> first, then;

		private Combinator(final Comparator<ArgNode<? extends State, ? extends Action>> first,
				final Comparator<ArgNode<? extends State, ? extends Action>> then) {
			this.first = first;
			this.then = then;
		}

		@Override
		public int compare(final ArgNode<? extends State, ? extends Action> n1,
				final ArgNode<? extends State, ? extends Action> n2) {
			final int compareFirst = first.compare(n1, n2);
			if (compareFirst != 0) {
				return compareFirst;
			} else {
				return then.compare(n1, n2);
			}

		}

	}
}
