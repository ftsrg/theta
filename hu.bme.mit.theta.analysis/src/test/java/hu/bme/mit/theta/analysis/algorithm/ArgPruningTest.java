package hu.bme.mit.theta.analysis.algorithm;

import static org.junit.Assert.assertEquals;

import org.junit.Test;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.Domain;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.utils.ArgVisualizer;
import hu.bme.mit.theta.common.visualization.GraphvizWriter;

public class ArgPruningTest {

	private final class NullState implements State {
		private final String label;

		public NullState(final String label) {
			this.label = label;
		}

		@Override
		public String toString() {
			return label;
		}
	}

	private final class NullAction implements Action {
	}

	private final class NullDomain implements Domain<State> {

		@Override
		public boolean isTop(final State state) {
			return false;
		}

		@Override
		public boolean isBottom(final State state) {
			return false;
		}

		@Override
		public boolean isLeq(final State state1, final State state2) {
			return false;
		}

	}

	@Test
	public void test() {
		final ARG<State, Action> arg = ARG.create(new NullDomain());

		final State s0 = new NullState("0");
		final State s00 = new NullState("00");
		final State s01 = new NullState("01");
		final State s02 = new NullState("02");
		final State s000 = new NullState("000");
		final State s001 = new NullState("001");

		final Action a = new NullAction();

		final ArgNode<State, Action> n0 = arg.createInitNode(s0, false);
		final ArgNode<State, Action> n00 = arg.createSuccNode(n0, a, s00, false);
		final ArgNode<State, Action> n01 = arg.createSuccNode(n0, a, s01, false);
		final ArgNode<State, Action> n02 = arg.createSuccNode(n0, a, s02, false);
		final ArgNode<State, Action> n000 = arg.createSuccNode(n00, a, s000, false);
		final ArgNode<State, Action> n001 = arg.createSuccNode(n00, a, s001, true);

		arg.cover(n000, n0);
		arg.cover(n01, n0);
		arg.cover(n02, n00);

		assertEquals(6, arg.getNodes().size());
		assertEquals(1, arg.getInitNodes().size());
		assertEquals(1, arg.getTargetNodes().size());
		assertEquals(n001, arg.getTargetNodes().iterator().next());
		assertEquals(2, n0.coveredNodes().size());

		System.out.println(new GraphvizWriter().writeString(ArgVisualizer.visualize(arg)));
		System.out.println("=========================");

		arg.prune(n00);

		assertEquals(3, arg.getNodes().size());
		assertEquals(1, arg.getInitNodes().size());
		assertEquals(0, arg.getTargetNodes().size());
		assertEquals(1, n0.coveredNodes.size());
		assertEquals(false, n02.getCoveringNode().isPresent());

		System.out.println(new GraphvizWriter().writeString(ArgVisualizer.visualize(arg)));
	}
}
