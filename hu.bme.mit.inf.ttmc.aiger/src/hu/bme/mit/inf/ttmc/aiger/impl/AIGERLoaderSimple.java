package hu.bme.mit.inf.ttmc.aiger.impl;

import static hu.bme.mit.inf.ttmc.formalism.common.expr.impl.Exprs2.Ref;

import java.io.BufferedReader;
import java.io.FileInputStream;
import java.io.IOException;
import java.io.InputStreamReader;
import java.util.ArrayList;
import java.util.List;

import com.google.common.collect.ImmutableSet;

import hu.bme.mit.inf.ttmc.aiger.AIGERLoader;
import hu.bme.mit.inf.ttmc.core.expr.Expr;
import hu.bme.mit.inf.ttmc.core.expr.impl.Exprs;
import hu.bme.mit.inf.ttmc.core.type.BoolType;
import hu.bme.mit.inf.ttmc.core.type.impl.Types;
import hu.bme.mit.inf.ttmc.formalism.common.decl.VarDecl;
import hu.bme.mit.inf.ttmc.formalism.common.decl.impl.Decls2;
import hu.bme.mit.inf.ttmc.formalism.common.expr.impl.Exprs2;
import hu.bme.mit.inf.ttmc.formalism.sts.STS;
import hu.bme.mit.inf.ttmc.formalism.sts.impl.STSImpl;

public class AIGERLoaderSimple implements AIGERLoader {

	@Override
	public STS load(final String fileName) throws IOException {

		final STSImpl.Builder builder = new STSImpl.Builder();
		final BufferedReader br = new BufferedReader(new InputStreamReader(new FileInputStream(fileName)));

		int maxVars, inputs, latches, outputs, andGates;
		// Parse header
		final String[] header = br.readLine().split(" ");
		maxVars = Integer.parseInt(header[1]);
		inputs = Integer.parseInt(header[2]);
		latches = Integer.parseInt(header[3]);
		outputs = Integer.parseInt(header[4]);
		andGates = Integer.parseInt(header[5]);
		// Create variables
		final List<VarDecl<BoolType>> vars = new ArrayList<>(maxVars + 1);
		final List<Expr<? extends BoolType>> outVars = new ArrayList<>(1);
		for (int i = 0; i <= maxVars; ++i)
			vars.add(Decls2.Var("v" + i, Types.Bool()));
		// v0 is the constant 'false'
		builder.addInvar(Exprs.Not(Ref(vars.get(0))));

		// Inputs
		for (int i = 0; i < inputs; ++i)
			br.readLine();

		// Latches
		for (int i = 0; i < latches; ++i) {
			final String v[] = br.readLine().split(" ");
			final int v1 = Integer.parseInt(v[0]);
			final int v2 = Integer.parseInt(v[1]);
			builder.addInit(Exprs.Not(Ref(vars.get(v1 / 2))));
			builder.addTrans(Exprs.Iff(Exprs2.Prime(Ref(vars.get(v1 / 2))),
					v2 % 2 == 0 ? Ref(vars.get(v2 / 2)) : Exprs.Not(Ref(vars.get(v2 / 2)))));
		}

		// Outputs
		for (int i = 0; i < outputs; ++i) {
			final int v = Integer.parseInt(br.readLine());
			outVars.add(v % 2 == 0 ? Ref(vars.get(v / 2)) : Exprs.Not(Ref(vars.get(v / 2))));
		}

		// And gates
		for (int i = 0; i < andGates; ++i) {
			final String[] v = br.readLine().split(" ");
			final int vo = Integer.parseInt(v[0]);
			final int vi1 = Integer.parseInt(v[1]);
			final int vi2 = Integer.parseInt(v[2]);
			builder.addInvar(
					Exprs.Iff(Ref(vars.get(vo / 2)),
							Exprs.And(ImmutableSet.of(
									vi1 % 2 == 0 ? Ref(vars.get(vi1 / 2)) : Exprs.Not(Ref(vars.get(vi1 / 2))),
									vi2 % 2 == 0 ? Ref(vars.get(vi2 / 2)) : Exprs.Not(Ref(vars.get(vi2 / 2)))))));
		}

		br.close();

		// Requirement
		if (outVars.size() == 1) {
			builder.setProp(Exprs.Not(outVars.get(0)));
		} else {
			throw new UnsupportedOperationException(
					"Currently only models with a single output variable are supported (this model has "
							+ outVars.size() + ").");
		}

		return builder.build();
	}
}
