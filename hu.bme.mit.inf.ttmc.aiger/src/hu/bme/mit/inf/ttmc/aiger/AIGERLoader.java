package hu.bme.mit.inf.ttmc.aiger;

import java.io.BufferedReader;
import java.io.FileInputStream;
import java.io.IOException;
import java.io.InputStreamReader;
import java.util.ArrayList;
import java.util.List;

import hu.bme.mit.inf.ttmc.aiger.elements.AndGate;
import hu.bme.mit.inf.ttmc.aiger.elements.FalseConst;
import hu.bme.mit.inf.ttmc.aiger.elements.HWElement;
import hu.bme.mit.inf.ttmc.aiger.elements.InVar;
import hu.bme.mit.inf.ttmc.aiger.elements.Latch;
import hu.bme.mit.inf.ttmc.aiger.elements.OutVar;
import hu.bme.mit.inf.ttmc.formalism.sts.STS;
import hu.bme.mit.inf.ttmc.formalism.sts.STSManager;
import hu.bme.mit.inf.ttmc.formalism.sts.impl.STSImpl;

public class AIGERLoader {
	public STS load(String fileName, STSManager manager) throws IOException {
		STSImpl.Builder builder = new STSImpl.Builder();
		BufferedReader br = new BufferedReader(new InputStreamReader(new FileInputStream(fileName)));
		
		int inputs, latches, outputs, andGates;
		// Parse header
		String[] header = br.readLine().split(" ");
		inputs = Integer.parseInt(header[2]);
		latches = Integer.parseInt(header[3]);
		outputs = Integer.parseInt(header[4]);
		andGates = Integer.parseInt(header[5]);
		
		List<HWElement> elements = new ArrayList<>(inputs + latches + andGates + 1);
		for (int i = 0; i < inputs + latches + andGates + 1; ++i) elements.add(null);
		elements.set(0, new FalseConst());
		List<OutVar> outVarElements = new ArrayList<>(outputs);
		List<Latch> latchElements = new ArrayList<>(latches);
		
		// Parse inputs
		for(int i = 0; i < inputs; ++i) {
			InVar inVar = new InVar(br.readLine(), manager);
			elements.set(inVar.getVarId(), inVar);
		}
		
		// Parse latches
		for (int i = 0; i < latches; ++i) {
			Latch latch = new Latch(br.readLine().split(" "), manager);
			elements.set(latch.getVarId(), latch);
			latchElements.add(latch);
		}
		
		// Parse outputs
		for (int i = 0; i < outputs; ++i) {
			OutVar outVar = new OutVar(br.readLine());
			outVarElements.add(outVar);
		}
		
		// Parse and gates
		for (int i = 0; i < andGates; ++i) {
			AndGate andGate = new AndGate(br.readLine().split(" "));
			elements.set(andGate.getVarId(), andGate);
		}

		br.close();
		
		// Process latches
		for (Latch latch : latchElements) {
			builder.addInit(latch.getInitExpr(manager));
			builder.addTrans(latch.getTransExpr(manager, elements));
		}
		
		// Process output
		if (outVarElements.size() == 1) {
			builder.setProp(manager.getExprFactory().Not(outVarElements.get(0).getExpr(manager, elements)));
		} else {
			throw new UnsupportedOperationException("Currently only models with a single output variable are supported (this model has " + outVarElements.size() + ").");
		}
		
		return builder.build();
	}

}
