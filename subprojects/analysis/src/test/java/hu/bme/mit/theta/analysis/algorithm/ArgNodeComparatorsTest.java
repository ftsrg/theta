/*
 *  Copyright 2017 Budapest University of Technology and Economics
 *  
 *  Licensed under the Apache License, Version 2.0 (the "License");
 *  you may not use this file except in compliance with the License.
 *  You may obtain a copy of the License at
 *  
 *      http://www.apache.org/licenses/LICENSE-2.0
 *  
 *  Unless required by applicable law or agreed to in writing, software
 *  distributed under the License is distributed on an "AS IS" BASIS,
 *  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *  See the License for the specific language governing permissions and
 *  limitations under the License.
 */
package hu.bme.mit.theta.analysis.algorithm;

import static hu.bme.mit.theta.analysis.algorithm.ArgNodeComparators.bfs;
import static hu.bme.mit.theta.analysis.algorithm.ArgNodeComparators.combine;
import static hu.bme.mit.theta.analysis.algorithm.ArgNodeComparators.creationAsc;
import static hu.bme.mit.theta.analysis.algorithm.ArgNodeComparators.creationDesc;
import static hu.bme.mit.theta.analysis.algorithm.ArgNodeComparators.dfs;
import static hu.bme.mit.theta.analysis.algorithm.ArgNodeComparators.targetFirst;

import java.util.List;
import java.util.stream.Collectors;

import org.junit.Assert;
import org.junit.Test;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.stubs.ActionStub;
import hu.bme.mit.theta.analysis.stubs.PartialOrdStub;
import hu.bme.mit.theta.analysis.stubs.StateStub;

public class ArgNodeComparatorsTest {

	private final ARG<State, Action> arg = ARG.create(new PartialOrdStub());
	private final Action act = new ActionStub("A");

	private final ArgNode<State, Action> s0 = arg.createInitNode(new StateStub("s0"), false);
	private final ArgNode<State, Action> s10 = arg.createSuccNode(s0, act, new StateStub("s10"), false);
	private final ArgNode<State, Action> s20 = arg.createSuccNode(s10, act, new StateStub("s20"), true);
	private final ArgNode<State, Action> s21 = arg.createSuccNode(s10, act, new StateStub("s21"), false);
	private final ArgNode<State, Action> s11 = arg.createSuccNode(s0, act, new StateStub("s11"), true);
	private final ArgNode<State, Action> s12 = arg.createSuccNode(s0, act, new StateStub("s12"), false);
	private final List<ArgNode<State, Action>> nodes = arg.getNodes().collect(Collectors.toList());

	@Test
	public void testBfs() {
		nodes.sort(bfs());
		Assert.assertArrayEquals(new ArgNode[] { s0, s10, s11, s12, s20, s21 }, nodes.toArray());
	}

	@Test
	public void testDfs() {
		nodes.sort(dfs());
		Assert.assertArrayEquals(new ArgNode[] { s20, s21, s10, s11, s12, s0 }, nodes.toArray());
	}

	@Test
	public void testCreationAsc() {
		nodes.sort(creationAsc());
		Assert.assertArrayEquals(new ArgNode[] { s0, s10, s20, s21, s11, s12 }, nodes.toArray());
	}

	@Test
	public void testCreationDesc() {
		nodes.sort(creationDesc());
		Assert.assertArrayEquals(new ArgNode[] { s12, s11, s21, s20, s10, s0 }, nodes.toArray());
	}

	@Test
	public void testTargetFirst() {
		nodes.sort(combine(targetFirst(), creationAsc()));
		Assert.assertArrayEquals(new ArgNode[] { s20, s11, s0, s10, s21, s12 }, nodes.toArray());
	}
}
