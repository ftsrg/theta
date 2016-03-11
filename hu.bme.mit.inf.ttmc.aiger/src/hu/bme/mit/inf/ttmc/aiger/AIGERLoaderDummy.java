package hu.bme.mit.inf.ttmc.aiger;

import java.io.BufferedReader;
import java.io.FileInputStream;
import java.io.IOException;
import java.io.InputStreamReader;
import java.util.ArrayList;
import java.util.List;

import com.google.common.collect.ImmutableSet;

import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.type.BoolType;
import hu.bme.mit.inf.ttmc.formalism.common.decl.VarDecl;
import hu.bme.mit.inf.ttmc.formalism.common.factory.VarDeclFactory;
import hu.bme.mit.inf.ttmc.formalism.sts.STS;
import hu.bme.mit.inf.ttmc.formalism.sts.STSManager;
import hu.bme.mit.inf.ttmc.formalism.sts.factory.STSExprFactory;
import hu.bme.mit.inf.ttmc.formalism.sts.impl.STSImpl;

public class AIGERLoaderDummy {
	public STS load(String fileName, STSManager manager) throws IOException {
		STSExprFactory ef = manager.getExprFactory();
		VarDeclFactory varDeclF = manager.getDeclFactory();
		
		STSImpl.Builder builder = new STSImpl.Builder();
		BufferedReader br = new BufferedReader(new InputStreamReader(new FileInputStream(fileName)));
		
		int maxVars, inputs, latches, outputs, andGates;
		// Parse header
		String[] header = br.readLine().split(" ");
		maxVars = Integer.parseInt(header[1]);
		inputs = Integer.parseInt(header[2]);
		latches = Integer.parseInt(header[3]);
		outputs = Integer.parseInt(header[4]);
		andGates = Integer.parseInt(header[5]);
		// Create variables
		List<VarDecl<BoolType>> vars = new ArrayList<>(maxVars + 1);
		List<Expr<? extends BoolType>> outVars = new ArrayList<>(1);
		for(int i = 0; i <= maxVars; ++i) vars.add(varDeclF.Var("v" + i, manager.getTypeFactory().Bool()));
		// v0 is the constant 'false'
		builder.addInvar(ef.Not(vars.get(0).getRef()));
		
		// Inputs
		for(int i = 0; i < inputs; ++i) br.readLine();
		
		// Latches
		for (int i = 0; i < latches; ++i) {
			String v[] = br.readLine().split(" ");
			int v1 = Integer.parseInt(v[0]);
			int v2 = Integer.parseInt(v[1]);
			builder.addInit(ef.Not(vars.get(v1/2).getRef()));
			builder.addTrans(ef.Iff(ef.Prime(vars.get(v1/2).getRef()),
					v2%2 == 0 ?
							vars.get(v2/2).getRef() :
							ef.Not(vars.get(v2/2).getRef())
					));
		}
		
		// Outputs
		for (int i = 0; i < outputs; ++i) {
			int v = Integer.parseInt(br.readLine());
			outVars.add(v%2 == 0 ? vars.get(v/2).getRef() : ef.Not(vars.get(v/2).getRef()));
		}
		
		// And gates
		for (int i = 0; i < andGates; ++i) {
			String[] v = br.readLine().split(" ");
			int vo = Integer.parseInt(v[0]);
			int vi1 = Integer.parseInt(v[1]);
			int vi2 = Integer.parseInt(v[2]);
			builder.addInvar(ef.Iff(vars.get(vo/2).getRef(),
					ef.And(ImmutableSet.of(
						vi1%2 == 0 ? vars.get(vi1/2).getRef() : ef.Not(vars.get(vi1/2).getRef()),
						vi2%2 == 0 ? vars.get(vi2/2).getRef() : ef.Not(vars.get(vi2/2).getRef())	
					))));
		}
		
		br.close();
		
		// Requirement
		if (outVars.size() == 1) {
			builder.setProp(ef.Not(outVars.get(0)));
		} else {
			throw new UnsupportedOperationException("Currently only models with a single output variable are supported (this model has " + outVars.size() + ").");
		}

		return builder.build();
	}
}
