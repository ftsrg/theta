package hu.bme.mit.inf.ttmc.aiger.impl;

import java.io.BufferedReader;
import java.io.FileInputStream;
import java.io.IOException;
import java.io.InputStreamReader;
import java.util.ArrayList;
import java.util.List;

import hu.bme.mit.inf.ttmc.aiger.AIGERLoader;
import hu.bme.mit.inf.ttmc.aiger.impl.elements.AndGate;
import hu.bme.mit.inf.ttmc.aiger.impl.elements.FalseConst;
import hu.bme.mit.inf.ttmc.aiger.impl.elements.HWElement;
import hu.bme.mit.inf.ttmc.aiger.impl.elements.InVar;
import hu.bme.mit.inf.ttmc.aiger.impl.elements.Latch;
import hu.bme.mit.inf.ttmc.aiger.impl.elements.OutVar;
import hu.bme.mit.inf.ttmc.formalism.sts.STS;
import hu.bme.mit.inf.ttmc.formalism.sts.STSManager;
import hu.bme.mit.inf.ttmc.formalism.sts.impl.STSImpl;

public class AIGERLoaderOptimized implements AIGERLoader {

	@Override
	public STS load(final String fileName, final STSManager manager) throws IOException {
		final STSImpl.Builder builder = new STSImpl.Builder(manager);
		final BufferedReader br = new BufferedReader(new InputStreamReader(new FileInputStream(fileName)));

		int inputs, latches, outputs, andGates;
		// Parse header
		final String[] header = br.readLine().split(" ");
		inputs = Integer.parseInt(header[2]);
		latches = Integer.parseInt(header[3]);
		outputs = Integer.parseInt(header[4]);
		andGates = Integer.parseInt(header[5]);

		final List<HWElement> elements = new ArrayList<>(inputs + latches + andGates + 1);
		for (int i = 0; i < inputs + latches + andGates + 1; ++i)
			elements.add(null);
		elements.set(0, new FalseConst());
		final List<OutVar> outVarElements = new ArrayList<>(outputs);
		final List<Latch> latchElements = new ArrayList<>(latches);

		// Parse inputs
		for (int i = 0; i < inputs; ++i) {
			final InVar inVar = new InVar(i + 1, br.readLine(), manager);
			elements.set(inVar.getVarId(), inVar);
		}

		// Parse latches
		for (int i = 0; i < latches; ++i) {
			final Latch latch = new Latch(i + 1, br.readLine().split(" "), manager);
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
			final AndGate andGate = new AndGate(br.readLine().split(" "));
			elements.set(andGate.getVarId(), andGate);
		}

		br.close();

		// Process latches
		for (final Latch latch : latchElements) {
			builder.addInit(latch.getInitExpr(manager));
			builder.addTrans(latch.getTransExpr(manager, elements));
		}

		// Process output
		if (outVarElements.size() == 1) {
			builder.setProp(manager.getExprFactory().Not(outVarElements.get(0).getExpr(manager, elements)));
		} else {
			throw new UnsupportedOperationException(
					"Currently only models with a single output variable are supported (this model has " + outVarElements.size() + ").");
		}

		return builder.build();
	}

}
