package hu.bme.mit.theta.analysis.algorithm;

import java.util.List;
import java.util.stream.Collectors;

import org.junit.Assert;
import org.junit.Test;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.stubs.ActionStub;
import hu.bme.mit.theta.analysis.stubs.DomainStub;
import hu.bme.mit.theta.analysis.stubs.StateStub;
import hu.bme.mit.theta.analysis.utils.ArgVisualizer;
import hu.bme.mit.theta.common.visualization.GraphvizWriter;

public class ArgNodeComparatorsTests {

	@Test
	public void test() {
		final ARG<State, Action> arg = ARG.create(new DomainStub());
		final Action act = new ActionStub("A");

		final ArgNode<State, Action> s0 = arg.createInitNode(new StateStub("s0"), false);
		final ArgNode<State, Action> s10 = arg.createSuccNode(s0, act, new StateStub("s10"), false);
		final ArgNode<State, Action> s20 = arg.createSuccNode(s10, act, new StateStub("s20"), false);
		final ArgNode<State, Action> s21 = arg.createSuccNode(s10, act, new StateStub("s21"), false);
		final ArgNode<State, Action> s11 = arg.createSuccNode(s0, act, new StateStub("s11"), false);
		final ArgNode<State, Action> s12 = arg.createSuccNode(s0, act, new StateStub("s12"), false);

		System.out.println(new GraphvizWriter().writeString(ArgVisualizer.visualize(arg)));

		final List<ArgNode<State, Action>> nodes = arg.getNodes().collect(Collectors.toList());

		nodes.sort(ArgNodeComparators.bfs());
		Assert.assertArrayEquals(new ArgNode[] { s0, s10, s11, s12, s20, s21 }, nodes.toArray());

		nodes.sort(ArgNodeComparators.dfs());
		Assert.assertArrayEquals(new ArgNode[] { s20, s21, s10, s11, s12, s0 }, nodes.toArray());

		nodes.sort(ArgNodeComparators.creationAsc());
		Assert.assertArrayEquals(new ArgNode[] { s0, s10, s20, s21, s11, s12 }, nodes.toArray());

		nodes.sort(ArgNodeComparators.creationDesc());
		Assert.assertArrayEquals(new ArgNode[] { s12, s11, s21, s20, s10, s0 }, nodes.toArray());
	}
}
