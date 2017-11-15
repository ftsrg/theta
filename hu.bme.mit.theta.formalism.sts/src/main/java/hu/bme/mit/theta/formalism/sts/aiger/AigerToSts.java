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

import static hu.bme.mit.theta.core.type.booltype.BoolExprs.And;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Iff;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Not;

import java.util.HashMap;
import java.util.Map;

import hu.bme.mit.theta.core.decl.Decls;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.anytype.Exprs;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.formalism.sts.STS;
import hu.bme.mit.theta.formalism.sts.STS.Builder;
import hu.bme.mit.theta.formalism.sts.aiger.elements.AigerNode;
import hu.bme.mit.theta.formalism.sts.aiger.elements.AigerSystem;
import hu.bme.mit.theta.formalism.sts.aiger.elements.AigerWire;
import hu.bme.mit.theta.formalism.sts.aiger.elements.AndGate;
import hu.bme.mit.theta.formalism.sts.aiger.elements.FalseConst;
import hu.bme.mit.theta.formalism.sts.aiger.elements.InputVar;
import hu.bme.mit.theta.formalism.sts.aiger.elements.Latch;

public final class AigerToSts {

	public static STS createSts(final AigerSystem aigerSys) {
		final Builder builder = STS.builder();

		final Map<AigerNode, VarDecl<BoolType>> vars = new HashMap<>();

		for (final AigerNode node : aigerSys.getNodes()) {
			vars.put(node, Decls.Var(node.getName(), Bool()));
		}

		for (final AigerNode node : aigerSys.getNodes()) {
			if (node instanceof InputVar) {
				// Do nothing
			} else if (node instanceof FalseConst) {
				builder.addInvar(Not(vars.get(node).getRef()));
			} else if (node instanceof Latch) {
				final Latch latch = (Latch) node;
				builder.addInit(Not(vars.get(latch).getRef()));
				final AigerWire inWire = latch.getInWire();
				final AigerNode source = inWire.getSource();
				final Expr<BoolType> lhs = Exprs.Prime(vars.get(latch).getRef());
				final Expr<BoolType> rhs = inWire.isPonated() ? vars.get(source).getRef()
						: Not(vars.get(source).getRef());
				builder.addTrans(Iff(lhs, rhs));
			} else if (node instanceof AndGate) {
				final AndGate andGate = (AndGate) node;
				final AigerWire inWire1 = andGate.getInWire1();
				final AigerWire inWire2 = andGate.getInWire2();
				final AigerNode source1 = inWire1.getSource();
				final AigerNode source2 = inWire2.getSource();
				final Expr<BoolType> lhs = vars.get(andGate).getRef();
				final Expr<BoolType> rhs1 = inWire1.isPonated() ? vars.get(source1).getRef()
						: Not(vars.get(source1).getRef());
				final Expr<BoolType> rhs2 = inWire2.isPonated() ? vars.get(source2).getRef()
						: Not(vars.get(source2).getRef());
				builder.addInvar(Iff(lhs, And(rhs1, rhs2)));
			} else {
				throw new UnsupportedOperationException("Unknown node: " + node.getClass().getName());
			}
		}

		final AigerWire outputWire = aigerSys.getOutput().getInWire();
		if (outputWire.isPonated()) {
			builder.setProp(Not(vars.get(outputWire.getSource()).getRef()));
		} else {
			builder.setProp(vars.get(outputWire.getSource()).getRef());
		}

		return builder.build();

	}

}
