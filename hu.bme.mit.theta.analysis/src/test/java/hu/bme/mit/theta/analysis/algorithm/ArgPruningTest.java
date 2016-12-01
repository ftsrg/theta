package hu.bme.mit.theta.analysis.algorithm;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;

import org.junit.Test;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.stubs.ActionStub;
import hu.bme.mit.theta.analysis.stubs.DomainStub;
import hu.bme.mit.theta.analysis.stubs.StateStub;
import hu.bme.mit.theta.analysis.utils.ArgVisualizer;
import hu.bme.mit.theta.common.visualization.GraphvizWriter;

public class ArgPruningTest {

	@Test
	public void test() {
		final ARG<State, Action> arg = ARG.create(new DomainStub());

		final State s0 = new StateStub("0");
		final State s00 = new StateStub("00");
		final State s01 = new StateStub("01");
		final State s02 = new StateStub("02");
		final State s000 = new StateStub("000");
		final State s001 = new StateStub("001");

		final Action a = new ActionStub("A");

		final ArgNode<State, Action> n0 = arg.createInitNode(s0, false);
		final ArgNode<State, Action> n00 = arg.createSuccNode(n0, a, s00, false);
		final ArgNode<State, Action> n01 = arg.createSuccNode(n0, a, s01, false);
		final ArgNode<State, Action> n02 = arg.createSuccNode(n0, a, s02, false);
		final ArgNode<State, Action> n000 = arg.createSuccNode(n00, a, s000, false);
		final ArgNode<State, Action> n001 = arg.createSuccNode(n00, a, s001, true);

		arg.cover(n000, n0);
		arg.cover(n01, n0);
		arg.cover(n02, n00);

		assertEquals(6, arg.getNodes().count());
		assertEquals(1, arg.getInitNodes().count());
		assertEquals(1, arg.getUnsafeNodes().count());
		assertEquals(n001, arg.getUnsafeNodes().iterator().next());
		assertEquals(2, n0.getCoveredNodes().size());

		System.out.println(new GraphvizWriter().writeString(ArgVisualizer.visualize(arg)));
		System.out.println("=========================");

		arg.prune(n00);

		assertEquals(3, arg.getNodes().count());
		assertEquals(1, arg.getInitNodes().count());
		assertEquals(0, arg.getUnsafeNodes().count());
		assertEquals(1, n0.coveredNodes.size());
		assertFalse(n02.getCoveringNode().isPresent());

		System.out.println(new GraphvizWriter().writeString(ArgVisualizer.visualize(arg)));
	}
}
