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
package hu.bme.mit.theta.formalism.sts.aiger;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Set;

import hu.bme.mit.theta.formalism.sts.aiger.elements.AigerNode;
import hu.bme.mit.theta.formalism.sts.aiger.elements.AigerSystem;
import hu.bme.mit.theta.formalism.sts.aiger.elements.AigerWire;

public final class AigerCoi {

	private AigerCoi() {
	}

	public static void apply(final AigerSystem system) {

		final Set<AigerNode> reachableNodes = new HashSet<>();
		final List<AigerNode> queue = new ArrayList<>();
		queue.add(system.getOutput());

		while (!queue.isEmpty()) {
			final AigerNode node = queue.remove(queue.size() - 1);
			if (!reachableNodes.contains(node)) {
				reachableNodes.add(node);
				for (final AigerWire wire : node.getInWires()) {
					final AigerNode source = wire.getSource();
					queue.add(source);
				}
			}
		}
		reachableNodes.remove(system.getOutput());

		for (final Iterator<AigerNode> iterator = system.getNodes().iterator(); iterator.hasNext();) {
			final AigerNode node = iterator.next();
			if (!reachableNodes.contains(node)) {
				iterator.remove();
				for (final AigerWire wire : node.getInWires()) {
					wire.getSource().removeOutWire(wire);
				}
			}

		}

		system.getNodes().clear();
		system.getNodes().addAll(reachableNodes);

	}

}
