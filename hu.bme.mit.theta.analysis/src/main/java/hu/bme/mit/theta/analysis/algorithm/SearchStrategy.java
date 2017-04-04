package hu.bme.mit.theta.analysis.algorithm;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.waitlist.PriorityWaitlist;
import hu.bme.mit.theta.analysis.waitlist.RandomWaitlist;
import hu.bme.mit.theta.analysis.waitlist.Waitlist;

public abstract class SearchStrategy {

	private SearchStrategy() {
	}

	public abstract <S extends State, A extends Action> Waitlist<ArgNode<S, A>> createWaitlist();

	public static SearchStrategy breadthFirst() {
		return BreadthFirst.INSTANCE;
	}

	public static SearchStrategy depthFirst() {
		return DepthFirst.INSTANCE;
	}

	public static SearchStrategy random() {
		return Random.INSTANCE;
	}

	public static final class BreadthFirst extends SearchStrategy {
		private static final BreadthFirst INSTANCE = new BreadthFirst();

		private BreadthFirst() {
		}

		@Override
		public <S extends State, A extends Action> Waitlist<ArgNode<S, A>> createWaitlist() {
			return PriorityWaitlist.create(ArgNodeComparators.bfs());
		}
	}

	public static final class DepthFirst extends SearchStrategy {
		private static final DepthFirst INSTANCE = new DepthFirst();

		private DepthFirst() {
		}

		@Override
		public <S extends State, A extends Action> Waitlist<ArgNode<S, A>> createWaitlist() {
			return PriorityWaitlist.create(ArgNodeComparators.dfs());
		}
	}

	public static final class Random extends SearchStrategy {
		private static final Random INSTANCE = new Random();

		private Random() {
		}

		@Override
		public <S extends State, A extends Action> Waitlist<ArgNode<S, A>> createWaitlist() {
			return RandomWaitlist.create();
		}
	}

}
