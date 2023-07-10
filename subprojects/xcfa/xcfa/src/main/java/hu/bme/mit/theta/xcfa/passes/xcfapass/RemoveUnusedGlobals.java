/*
 *  Copyright 2023 Budapest University of Technology and Economics
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

package hu.bme.mit.theta.xcfa.passes.xcfapass;

import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.xcfa.model.XCFA;
import hu.bme.mit.theta.xcfa.model.XcfaEdge;
import hu.bme.mit.theta.xcfa.model.XcfaLabel;
import hu.bme.mit.theta.xcfa.model.XcfaProcedure;
import hu.bme.mit.theta.xcfa.model.XcfaProcess;

import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.stream.Collectors;

import static hu.bme.mit.theta.xcfa.passes.procedurepass.Utils.getVars;

public class RemoveUnusedGlobals extends XcfaPass {
	@Override
	public XCFA.Builder run(XCFA.Builder builder) {
		Set<VarDecl<?>> usedGlobals = new LinkedHashSet<>();
		for (XcfaProcess.Builder process : builder.getProcesses()) {
			for (XcfaProcedure.Builder procedure : process.getProcedures()) {
				for (XcfaEdge edge : procedure.getEdges()) {
					for (XcfaLabel label : edge.getLabels()) {
						usedGlobals.addAll(getVars(label));
					}
				}
			}
		}
		Set<Map.Entry<VarDecl<?>, Optional<LitExpr<?>>>> newGlobals = builder.getGlobalVars().entrySet().stream().filter(varDeclOptionalEntry -> usedGlobals.contains(varDeclOptionalEntry.getKey())).collect(Collectors.toSet());
		builder.getGlobalVars().clear();
		for (Map.Entry<VarDecl<?>, Optional<LitExpr<?>>> newGlobal : newGlobals) {
			builder.addGlobalVar(newGlobal.getKey(), newGlobal.getValue().orElse(null));
		}
		return builder;
	}
}
