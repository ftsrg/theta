package hu.bme.mit.inf.ttmc.aiger;

import java.io.BufferedReader;
import java.io.FileInputStream;
import java.io.IOException;
import java.io.InputStreamReader;
import java.util.ArrayList;
import java.util.List;

import com.google.common.collect.ImmutableSet;

import hu.bme.mit.inf.ttmc.constraint.ConstraintManager;
import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.factory.ExprFactory;
import hu.bme.mit.inf.ttmc.constraint.type.BoolType;
import hu.bme.mit.inf.ttmc.formalism.common.decl.VarDecl;
import hu.bme.mit.inf.ttmc.formalism.common.factory.STSFactory;
import hu.bme.mit.inf.ttmc.formalism.sts.STS;
import hu.bme.mit.inf.ttmc.formalism.sts.impl.STSImpl;

public class AIGERLoader {
	public STS load(String fileName, STSFactory stsFactory, ConstraintManager manager) throws IOException {
		STSImpl.Builder builder = new STSImpl.Builder();
		BufferedReader br = new BufferedReader(new InputStreamReader(new FileInputStream(fileName)));
		ExprFactory ef = manager.getExprFactory();
		
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
		for(int i = 0; i <= maxVars; ++i) vars.add(stsFactory.Var("v" + i, manager.getTypeFactory().Bool()));
		// v0 is the constant 'false'
		builder.addInvar(ef.Not(stsFactory.Ref(vars.get(0))));
		
		// Inputs
		for(int i = 0; i < inputs; ++i) br.readLine();
		
		// Latches
		for (int i = 0; i < latches; ++i) {
			String v[] = br.readLine().split(" ");
			int v1 = Integer.parseInt(v[0]);
			int v2 = Integer.parseInt(v[1]);
			builder.addInit(ef.Not(stsFactory.Ref(vars.get(v1/2))));
			builder.addTrans(ef.Iff(stsFactory.Prime(stsFactory.Ref(vars.get(v1/2))),
					v2%2 == 0 ?
							stsFactory.Ref(vars.get(v2/2)) :
							ef.Not(stsFactory.Ref(vars.get(v2/2)))
					));
		}
		
		// Outputs
		for (int i = 0; i < outputs; ++i) {
			int v = Integer.parseInt(br.readLine());
			outVars.add(v%2 == 0 ? stsFactory.Ref(vars.get(v/2)) : ef.Not(stsFactory.Ref(vars.get(v/2))));
		}
		
		// And gates
		for (int i = 0; i < andGates; ++i) {
			String[] v = br.readLine().split(" ");
			int vo = Integer.parseInt(v[0]);
			int vi1 = Integer.parseInt(v[1]);
			int vi2 = Integer.parseInt(v[2]);
			builder.addInvar(ef.Iff(stsFactory.Ref(vars.get(vo/2)),
					ef.And(ImmutableSet.of(
						vi1%2 == 0 ? stsFactory.Ref(vars.get(vi1/2)) : ef.Not(stsFactory.Ref(vars.get(vi1/2))),
						vi2%2 == 0 ? stsFactory.Ref(vars.get(vi2/2)) : ef.Not(stsFactory.Ref(vars.get(vi2/2)))	
					))));
		}
		
		br.close();
		
		// Requirement
		if (outVars.size() == 1) {
			builder.setProp(ef.Not(outVars.get(0)));
		} else {
			throw new UnsupportedOperationException("Currently only models with a single output variable are supported (this model has " + outVars.size() + ").");
		}
		
		// Variables
		builder.addVar(vars);
		
	
		return builder.build();
	}
}
