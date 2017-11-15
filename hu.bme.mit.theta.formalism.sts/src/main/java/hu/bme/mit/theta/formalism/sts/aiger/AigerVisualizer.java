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

import static java.lang.System.lineSeparator;

import java.util.HashSet;
import java.util.Set;

import hu.bme.mit.theta.formalism.sts.aiger.elements.AigerNode;
import hu.bme.mit.theta.formalism.sts.aiger.elements.AigerSystem;
import hu.bme.mit.theta.formalism.sts.aiger.elements.AigerWire;
import hu.bme.mit.theta.formalism.sts.aiger.elements.AndGate;
import hu.bme.mit.theta.formalism.sts.aiger.elements.FalseConst;
import hu.bme.mit.theta.formalism.sts.aiger.elements.InputVar;
import hu.bme.mit.theta.formalism.sts.aiger.elements.Latch;

public final class AigerVisualizer {

	private static final String INPUTSHAPE = "invhouse";
	private static final String LATCHSHAPE = "rectangle";
	private static final String OUTPUTSHAPE = "invhouse";
	private static final String ANDSHAPE = "ellipse";
	private static final String INVHEAD = "odot";

	private AigerVisualizer() {
	}

	public static String visualize(final AigerSystem system) {
		final StringBuilder sb = new StringBuilder();
		sb.append("digraph \"aiger\" {" + lineSeparator());

		final Set<AigerWire> wires = new HashSet<>();

		for (final AigerNode node : system.getNodes()) {
			if (node instanceof InputVar || node instanceof FalseConst) {
				sb.append(
						String.format("\t%s [shape=\"%s\", margin=\"0\", width=\"0\", height=\"0\"];" + lineSeparator(),
								node.getName(), INPUTSHAPE));
			} else if (node instanceof Latch) {
				sb.append(String.format(
						"\t%s [shape=\"%s\", margin=\"0.05\", width=\"0\", height=\"0\"];" + lineSeparator(),
						node.getName(), LATCHSHAPE));
			} else if (node instanceof AndGate) {
				sb.append(String.format(
						"\t%s [shape=\"%s\", margin=\"0.02\", width=\"0\", height=\"0\"];" + lineSeparator(),
						node.getName(), ANDSHAPE));
			} else {
				throw new UnsupportedOperationException("Unknown node: " + node.getClass().getName());
			}

			wires.addAll(node.getInWires());
			wires.addAll(node.getOutWires());
		}

		sb.append(String.format("\t%s [shape=\"%s\", margin=\"0\", width=\"0\", height=\"0\"];" + lineSeparator(),
				system.getOutput().getName(), OUTPUTSHAPE));
		wires.addAll(system.getOutput().getInWires());

		for (final AigerWire wire : wires) {
			sb.append(String.format("\t%s -> %s", wire.getSource().getName(), wire.getTarget().getName()));
			if (!wire.isPonated()) {
				sb.append(" [arrowhead=\"" + INVHEAD + "\"]");
			}
			sb.append(lineSeparator());
		}

		sb.append("}");
		return sb.toString();
	}
}
