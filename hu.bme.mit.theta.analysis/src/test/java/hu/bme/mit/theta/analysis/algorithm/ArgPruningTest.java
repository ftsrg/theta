package hu.bme.mit.theta.analysis.algorithm;

import static org.junit.Assert.assertEquals;

import org.junit.Test;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.utils.ArgVisualizer;
import hu.bme.mit.theta.common.visualization.GraphVizWriter;

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

	@Test
	public void test() {
		final ARG<State, Action> arg = new ARG<>();

		final State s0 = new NullState("0");
		final State s00 = new NullState("00");
		final State s01 = new NullState("01");
		final State s000 = new NullState("000");
		final State s001 = new NullState("001");

		final Action a = new NullAction();

		final ArgNode<State, Action> n0 = arg.createInitNode(s0, false);
		final ArgNode<State, Action> n00 = arg.createSuccNode(n0, a, s00, false);
		final ArgNode<State, Action> n01 = arg.createSuccNode(n0, a, s01, false);
		final ArgNode<State, Action> n000 = arg.createSuccNode(n00, a, s000, false);
		final ArgNode<State, Action> n001 = arg.createSuccNode(n00, a, s001, true);

		n000.coverWith(n0);
		n01.coverWith(n0);

		assertEquals(5, arg.getNodes().size());
		assertEquals(1, arg.getInitNodes().size());
		assertEquals(1, arg.getTargetNodes().size());
		assertEquals(n001, arg.getTargetNodes().iterator().next());

		System.out.println(new GraphVizWriter().writeString(ArgVisualizer.visualize(arg)));
		System.out.println("=========================");

		arg.prune(n00);

		assertEquals(2, arg.getNodes().size());
		assertEquals(1, arg.getInitNodes().size());
		assertEquals(0, arg.getTargetNodes().size());

		System.out.println(new GraphVizWriter().writeString(ArgVisualizer.visualize(arg)));
	}
}
