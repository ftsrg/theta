package hu.bme.mit.theta.analysis.algorithm;

import java.io.Serializable;
import java.util.Comparator;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.State;

public class ArgNodeComparators {

	private ArgNodeComparators() {
	}

	public static interface ArgNodeComparator
			extends Comparator<ArgNode<? extends State, ? extends Action>>, Serializable {
	}

	////

	public static ArgNodeComparator creationAsc() {
		return new CreationOrder();
	}

	public static ArgNodeComparator creationDesc() {
		return invert(creationAsc());
	}

	public static ArgNodeComparator invert(final ArgNodeComparator comparator) {
		return new Inverter(comparator);
	}

	public static ArgNodeComparator combine(final ArgNodeComparator first, final ArgNodeComparator then) {
		return new Combinator(first, then);
	}

	public static ArgNodeComparator bfs() {
		return combine(new DepthOrder(), new CreationOrder());
	}

	public static ArgNodeComparator dfs() {
		return combine(invert(new DepthOrder()), new CreationOrder());
	}

	public static ArgNodeComparator targetFirst() {
		return new TargetFirst();
	}

	////

	private static final class DepthOrder implements ArgNodeComparator {
		private static final long serialVersionUID = 6538293612674961734L;

		@Override
		public int compare(final ArgNode<? extends State, ? extends Action> n1,
				final ArgNode<? extends State, ? extends Action> n2) {
			return Integer.compare(n1.getDepth(), n2.getDepth());
		}
	}

	private static final class CreationOrder implements ArgNodeComparator {
		private static final long serialVersionUID = -8221009565128954827L;

		@Override
		public int compare(final ArgNode<? extends State, ? extends Action> n1,
				final ArgNode<? extends State, ? extends Action> n2) {
			return Integer.compare(n1.getId(), n2.getId());
		}
	}

	private static final class TargetFirst implements ArgNodeComparator {
		private static final long serialVersionUID = 4913094714715832187L;

		@Override
		public int compare(final ArgNode<? extends State, ? extends Action> n1,
				final ArgNode<? extends State, ? extends Action> n2) {
			return Boolean.compare(n1.isTarget(), n2.isTarget()) * -1;
		}
	}

	private static final class Inverter implements ArgNodeComparator {
		private static final long serialVersionUID = -4371396024975241987L;
		private final ArgNodeComparator comparator;

		private Inverter(final ArgNodeComparator comparator) {
			this.comparator = comparator;
		}

		@Override
		public int compare(final ArgNode<? extends State, ? extends Action> n1,
				final ArgNode<? extends State, ? extends Action> n2) {
			return comparator.compare(n1, n2) * -1;
		}
	}

	private static final class Combinator implements ArgNodeComparator {
		private static final long serialVersionUID = 732184663163863464L;
		private final ArgNodeComparator first, then;

		private Combinator(final ArgNodeComparator first, final ArgNodeComparator then) {
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
