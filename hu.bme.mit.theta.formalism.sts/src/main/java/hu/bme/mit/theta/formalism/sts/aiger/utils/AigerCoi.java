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
package hu.bme.mit.theta.formalism.sts.aiger.utils;

import java.util.ArrayDeque;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Queue;
import java.util.Set;

import hu.bme.mit.theta.formalism.sts.aiger.elements.AigerNode;
import hu.bme.mit.theta.formalism.sts.aiger.elements.AigerSystem;
import hu.bme.mit.theta.formalism.sts.aiger.elements.AigerWire;

/**
 * Cone-of-influence (COI) reduction for AIGER systems.
 */
public final class AigerCoi {

	private AigerCoi() {
	}

	/**
	 * Apply COI reduction to the system by removing nodes that are not backward
	 * reachable from the output. The parameter is modified.
	 *
	 * @param system
	 */
	public static void apply(final AigerSystem system) {
		final Set<AigerNode> reachable = getReachableNodes(system);
		pruneUnreachableNodes(system, reachable);
	}

	private static Set<AigerNode> getReachableNodes(final AigerSystem system) {
		final Set<AigerNode> reached = new HashSet<>();
		final Queue<AigerNode> queue = new ArrayDeque<>();
		queue.add(system.getOutput());

		while (!queue.isEmpty()) {
			final AigerNode node = queue.remove();
			if (!reached.contains(node)) {
				reached.add(node);
				node.getInWires().forEach(w -> queue.add(w.getSource()));
			}
		}
		reached.remove(system.getOutput());
		return reached;
	}

	private static void pruneUnreachableNodes(final AigerSystem system, final Set<AigerNode> reachable) {
		system.getNodes().clear();
		system.getNodes().addAll(reachable);
		for (final AigerNode node : system.getNodes()) {
			for (final Iterator<AigerWire> iterator = node.getOutWires().iterator(); iterator.hasNext();) {
				final AigerWire wire = iterator.next();
				if (!reachable.contains(wire.getTarget())) {
					iterator.remove();
				}
			}
		}
	}
}
