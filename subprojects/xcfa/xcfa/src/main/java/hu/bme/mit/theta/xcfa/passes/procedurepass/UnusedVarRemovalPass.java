/*
 * Copyright 2021 Budapest University of Technology and Economics
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package hu.bme.mit.theta.xcfa.passes.procedurepass;

import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.xcfa.model.XcfaEdge;
import hu.bme.mit.theta.xcfa.model.XcfaLabel;
import hu.bme.mit.theta.xcfa.model.XcfaProcedure;

import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;

import static hu.bme.mit.theta.xcfa.passes.procedurepass.Utils.getModifiedVars;
import static hu.bme.mit.theta.xcfa.passes.procedurepass.Utils.getVars;

public class UnusedVarRemovalPass extends ProcedurePass {
	@Override
	public XcfaProcedure.Builder run(XcfaProcedure.Builder builder) {
		removeUnusedVars(builder, null);
		return builder;
	}

	public static void removeUnusedVars(XcfaProcedure.Builder builder, Set<VarDecl<?>> usedVars) {
		boolean atLeastOne = true;
		while(atLeastOne) {
			atLeastOne = false;
			Set<VarDecl<?>> vars;
			if(usedVars == null) {
				vars = new LinkedHashSet<>();
				for (XcfaEdge edge : builder.getEdges()) {
					for (XcfaLabel label : edge.getLabels()) {
						Set<VarDecl<?>> vars1 = new LinkedHashSet<>(getVars(label));
						Set<VarDecl<?>> modifiedVars = getModifiedVars(label);
						vars1.removeIf(varDecl ->
								modifiedVars.contains(varDecl) &&
								!builder.getParams().containsKey(varDecl) &&
								builder.getLocalVars().containsKey(varDecl)
						);
						vars.addAll(vars1);
					}
				}
			} else vars = usedVars;
			List<XcfaEdge> edges = new ArrayList<>(builder.getEdges());
			for (XcfaEdge edge : edges) {
				XcfaEdge newEdge = edge.mapLabels(label -> {
//					if (getModifiedVars(label).containsAll(vars)) {
//						return Stmt(Skip());
//					} else return label;
					return label;
				});
				if (!edge.getLabels().equals(newEdge.getLabels())) {
					atLeastOne = true;
					builder.removeEdge(edge);
					builder.addEdge(newEdge);
				}
			}
			List<VarDecl<?>> unused = builder.getLocalVars().keySet().stream().filter(var -> !vars.contains(var)).collect(Collectors.toList());
			for (VarDecl<?> varDecl : unused) {
				builder.getLocalVars().remove(varDecl);
			}
		}
	}
}
