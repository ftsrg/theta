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

import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Not;

import java.io.BufferedReader;
import java.io.FileInputStream;
import java.io.IOException;
import java.io.InputStreamReader;
import java.util.ArrayList;
import java.util.List;

import hu.bme.mit.theta.formalism.sts.STS;
import hu.bme.mit.theta.formalism.sts.aiger.elements.AndGate;
import hu.bme.mit.theta.formalism.sts.aiger.elements.FalseConst;
import hu.bme.mit.theta.formalism.sts.aiger.elements.HwElement;
import hu.bme.mit.theta.formalism.sts.aiger.elements.InVar;
import hu.bme.mit.theta.formalism.sts.aiger.elements.Latch;
import hu.bme.mit.theta.formalism.sts.aiger.elements.OutVar;

/**
 * A compacting AIGER parser that minimizes the number of STS variables used. It
 * only associates a STS variable to inputs and latches. Note, that the reduced
 * number of variables may not be suitable for each algorithm. It supports AIGER
 * format 1.7.
 */
public class CompactingAigerParser implements AigerParser {

	@Override
	public STS parse(final String fileName) throws IOException {
		final STS.Builder builder = STS.builder();
		final BufferedReader br = new BufferedReader(new InputStreamReader(new FileInputStream(fileName)));

		try {
			final int inputs;
			int latches;
			int outputs;
			int andGates;
			// Parse header
			final String[] header = checkNotNull(br.readLine(), "Header expected").split(" ");
			inputs = Integer.parseInt(header[2]);
			latches = Integer.parseInt(header[3]);
			outputs = Integer.parseInt(header[4]);
			andGates = Integer.parseInt(header[5]);

			final List<HwElement> elements = new ArrayList<>(inputs + latches + andGates + 1);
			for (int i = 0; i < inputs + latches + andGates + 1; ++i) {
				elements.add(null);
			}
			elements.set(0, new FalseConst());
			final List<OutVar> outVarElements = new ArrayList<>(outputs);
			final List<Latch> latchElements = new ArrayList<>(latches);

			// Parse inputs
			for (int i = 0; i < inputs; ++i) {
				final InVar inVar = new InVar(i + 1, br.readLine());
				elements.set(inVar.getVarId(), inVar);
			}

			// Parse latches
			for (int i = 0; i < latches; ++i) {
				final Latch latch = new Latch(i + 1, checkNotNull(br.readLine(), "Latch expected").split(" "));
				elements.set(latch.getVarId(), latch);
				latchElements.add(latch);
			}

			// Parse outputs
			for (int i = 0; i < outputs; ++i) {
				final OutVar outVar = new OutVar(br.readLine());
				outVarElements.add(outVar);
			}

			// Parse and gates
			for (int i = 0; i < andGates; ++i) {
				final AndGate andGate = new AndGate(checkNotNull(br.readLine(), "And gate expected").split(" "));
				elements.set(andGate.getVarId(), andGate);
			}

			// Process latches
			for (final Latch latch : latchElements) {
				builder.addInit(latch.getInitExpr());
				builder.addTrans(latch.getTransExpr(elements));
			}

			// Process output
			if (outVarElements.size() == 1) {
				builder.setProp(Not(outVarElements.get(0).getExpr(elements)));
			} else {
				throw new UnsupportedOperationException(
						"Currently only models with a single output variable are supported (this model has "
								+ outVarElements.size() + ").");
			}

			return builder.build();
		} finally {
			br.close();
		}
	}

}
