package hu.bme.mit.theta.analysis.algorithm;

import java.util.Comparator;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.State;

public abstract class ArgNodeComparator<S extends State, A extends Action> implements Comparator<ArgNode<S, A>> {

	private ArgNodeComparator() {
	}

	public static <S extends State, A extends Action> ArgNodeComparator<S, A> depthFirst() {
		return new DepthFirst<>();
	}

	public static <S extends State, A extends Action> ArgNodeComparator<S, A> breadthFirst() {
		return new BreadthFirst<>();
	}

	public static final class DepthFirst<S extends State, A extends Action> extends ArgNodeComparator<S, A> {

		private DepthFirst() {
		}

		@Override
		public int compare(final ArgNode<S, A> n1, final ArgNode<S, A> n2) {
			if (n1.getDepth() < n2.getDepth()) {
				return -1;
			} else if (n1.getDepth() > n2.getDepth()) {
				return 1;
			} else {
				return 0;
			}
		}

	}

	public static final class BreadthFirst<S extends State, A extends Action> extends ArgNodeComparator<S, A> {

		private BreadthFirst() {
		}

		@Override
		public int compare(final ArgNode<S, A> n1, final ArgNode<S, A> n2) {
			if (n1.getDepth() < n2.getDepth()) {
				return 1;
			} else if (n1.getDepth() > n2.getDepth()) {
				return -1;
			} else {
				return 0;
			}
		}

	}

}
