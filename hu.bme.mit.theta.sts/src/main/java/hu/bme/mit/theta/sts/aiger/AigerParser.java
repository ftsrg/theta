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
package hu.bme.mit.theta.sts.aiger;

import static com.google.common.base.Preconditions.checkNotNull;
import static java.lang.Integer.parseInt;

import java.io.BufferedReader;
import java.io.FileInputStream;
import java.io.IOException;
import java.io.InputStreamReader;
import java.util.ArrayList;
import java.util.List;

import hu.bme.mit.theta.sts.aiger.elements.AigerNode;
import hu.bme.mit.theta.sts.aiger.elements.AigerSystem;
import hu.bme.mit.theta.sts.aiger.elements.AigerWire;
import hu.bme.mit.theta.sts.aiger.elements.AndGate;
import hu.bme.mit.theta.sts.aiger.elements.FalseConst;
import hu.bme.mit.theta.sts.aiger.elements.InputVar;
import hu.bme.mit.theta.sts.aiger.elements.Latch;
import hu.bme.mit.theta.sts.aiger.elements.OutputVar;

/**
 * Parser for textual (.aag) AIGER files.
 */
public final class AigerParser {

	private AigerParser() {
	}

	/**
	 * Parse a textual AIGER file (*.aag) to our internal representation.
	 *
	 * @param fileName Path of the AIGER file
	 * @return AIGER system internal representation
	 * @throws IOException
	 */
	public static AigerSystem parse(final String fileName) throws IOException {
		final BufferedReader br = new BufferedReader(new InputStreamReader(new FileInputStream(fileName)));

		try {
			int nNodes;
			int nInputs;
			int nLatches;
			int nOutputs;
			int nAndGates;
			// Parse header
			final String[] header = checkNotNull(br.readLine(), "Header expected").split(" ");
			nNodes = parseInt(header[1]);
			nInputs = parseInt(header[2]);
			nLatches = parseInt(header[3]);
			nOutputs = parseInt(header[4]);
			nAndGates = parseInt(header[5]);

			if (nOutputs != 1) {
				throw new UnsupportedOperationException("Only a single output variable is supported.");
			}

			final AigerNode[] nodes = new AigerNode[nNodes + 1];
			nodes[0] = new FalseConst();

			// Read inputs
			for (int i = 0; i < nInputs; ++i) {
				final String tokens[] = checkNotNull(br.readLine(), "Input expected").split(" ");
				final int varId = parseInt(tokens[0]) / 2;
				nodes[varId] = new InputVar(i + 1, varId);
			}

			// Read latches
			final List<Latch> latches = new ArrayList<>(nLatches);
			final List<Integer> latchInputs = new ArrayList<>(nLatches);
			for (int i = 0; i < nLatches; ++i) {
				final String tokens[] = checkNotNull(br.readLine(), "Latch expected").split(" ");
				final int varId = parseInt(tokens[0]) / 2;
				final Latch latch = new Latch(i + 1, varId);
				latches.add(latch);
				latchInputs.add(parseInt(tokens[1]));
				nodes[varId] = latch;
			}

			// Read output
			final OutputVar outputVar = new OutputVar(1);
			final int outputVarInput = parseInt(br.readLine());

			// Read and gates
			final List<AndGate> andGates = new ArrayList<>(nAndGates);
			final List<Integer> andGateInputs1 = new ArrayList<>(nAndGates);
			final List<Integer> andGateInputs2 = new ArrayList<>(nAndGates);
			for (int i = 0; i < nAndGates; ++i) {
				final String tokens[] = checkNotNull(br.readLine(), "And gate expected").split(" ");
				final int varId = parseInt(tokens[0]) / 2;
				final AndGate andGate = new AndGate(i + 1, varId);
				andGates.add(andGate);
				andGateInputs1.add(parseInt(tokens[1]));
				andGateInputs2.add(parseInt(tokens[2]));
				nodes[varId] = andGate;
			}

			for (final AigerNode node : nodes) {
				checkNotNull(node, "Missing node");
			}

			// Create connections for latches
			for (int i = 0; i < latches.size(); i++) {
				final Latch latch = latches.get(i);
				final AigerNode source = nodes[latchInputs.get(i) / 2];
				final AigerWire wire = new AigerWire(source, latch, latchInputs.get(i) % 2 == 0);
				latch.setInWire(wire);
				source.addOutWire(wire);
			}

			// Create connections for output
			{
				final AigerNode source = nodes[outputVarInput / 2];
				final AigerWire wire = new AigerWire(source, outputVar, outputVarInput % 2 == 0);
				outputVar.setInWire(wire);
				source.addOutWire(wire);
			}

			// Create connections for and gates
			for (int i = 0; i < andGates.size(); i++) {
				final AndGate andGate = andGates.get(i);
				final AigerNode source1 = nodes[andGateInputs1.get(i) / 2];
				final AigerNode source2 = nodes[andGateInputs2.get(i) / 2];
				final AigerWire wire1 = new AigerWire(source1, andGate, andGateInputs1.get(i) % 2 == 0);
				final AigerWire wire2 = new AigerWire(source2, andGate, andGateInputs2.get(i) % 2 == 0);
				andGate.setInWire1(wire1);
				andGate.setInWire2(wire2);
				source1.addOutWire(wire1);
				source2.addOutWire(wire2);
			}

			final List<AigerNode> nodeList = new ArrayList<>();
			for (final AigerNode node : nodes) {
				nodeList.add(node);
			}
			return new AigerSystem(nodeList, outputVar);
		} finally {
			br.close();
		}
	}
}
