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
package hu.bme.mit.theta.sts.aiger.utils;

import static java.lang.System.lineSeparator;

import java.util.HashSet;
import java.util.Set;

import hu.bme.mit.theta.sts.aiger.elements.AigerNode;
import hu.bme.mit.theta.sts.aiger.elements.AigerSystem;
import hu.bme.mit.theta.sts.aiger.elements.AigerWire;
import hu.bme.mit.theta.sts.aiger.elements.AndGate;
import hu.bme.mit.theta.sts.aiger.elements.FalseConst;
import hu.bme.mit.theta.sts.aiger.elements.InputVar;
import hu.bme.mit.theta.sts.aiger.elements.Latch;

/**
 * Visualizer for AIGER systems.
 */
public final class AigerVisualizer {

	private static final String INPUTNODE = "\t%s [shape=invhouse,margin=0,width=0,height=0];" + lineSeparator();
	private static final String LATCHNODE = "\t%s [shape=rectangle,margin=0.05,width=0,height=0];" + lineSeparator();
	private static final String OUTPUTNODE = INPUTNODE;
	private static final String ANDNODE = "\t%s [shape=ellipse,margin=0.02,width=0,height=0];" + lineSeparator();
	private static final String INVHEAD = "odot";

	private AigerVisualizer() {
	}

	/**
	 * Visualize an AIGER system in dot format.
	 *
	 * @param system
	 * @return
	 */
	public static String visualize(final AigerSystem system) {
		final StringBuilder sb = new StringBuilder();
		sb.append("digraph aiger {").append(lineSeparator());
		appendNodes(system, sb);
		appendWires(system, sb);
		sb.append('}');
		return sb.toString();
	}

	private static void appendNodes(final AigerSystem system, final StringBuilder sb) {
		for (final AigerNode node : system.getNodes()) {
			if (node instanceof InputVar || node instanceof FalseConst) {
				sb.append(String.format(INPUTNODE, node.getName()));
			} else if (node instanceof Latch) {
				sb.append(String.format(LATCHNODE, node.getName()));
			} else if (node instanceof AndGate) {
				sb.append(String.format(ANDNODE, node.getName()));
			} else {
				throw new UnsupportedOperationException("Unknown node: " + node.getClass().getName());
			}
		}
		sb.append(String.format(OUTPUTNODE, system.getOutput().getName()));
	}

	private static void appendWires(final AigerSystem system, final StringBuilder sb) {
		final Set<AigerWire> wires = new HashSet<>();
		system.getNodes().forEach(n -> wires.addAll(n.getInWires()));
		system.getNodes().forEach(n -> wires.addAll(n.getOutWires()));
		wires.addAll(system.getOutput().getInWires());
		for (final AigerWire wire : wires) {
			sb.append(String.format("\t%s -> %s", wire.getSource().getName(), wire.getTarget().getName()));
			if (!wire.isPonated()) {
				sb.append(" [arrowhead=" + INVHEAD + "]");
			}
			sb.append(';').append(lineSeparator());
		}
	}
}
