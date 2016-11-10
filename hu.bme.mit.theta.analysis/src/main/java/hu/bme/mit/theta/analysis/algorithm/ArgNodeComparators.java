package hu.bme.mit.theta.analysis.algorithm;

import java.util.Comparator;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.State;

public class ArgNodeComparators {

	private ArgNodeComparators() {
	}

	public static <S extends State, A extends Action> Comparator<ArgNode<S, A>> depthFirst() {
		return new DepthFirst<>();
	}

	public static <S extends State, A extends Action> Comparator<ArgNode<S, A>> breadthFirst() {
		return new BreadthFirst<>();
	}

	public static <S extends State, A extends Action> Comparator<ArgNode<S, A>> creationOrder() {
		return new CreationOrder<>();
	}

	private static final class DepthFirst<S extends State, A extends Action> implements Comparator<ArgNode<S, A>> {
		@Override
		public int compare(final ArgNode<S, A> n1, final ArgNode<S, A> n2) {
			return Integer.compare(n1.getDepth(), n2.getDepth()) * -1;
		}
	}

	private static final class BreadthFirst<S extends State, A extends Action> implements Comparator<ArgNode<S, A>> {
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

}
