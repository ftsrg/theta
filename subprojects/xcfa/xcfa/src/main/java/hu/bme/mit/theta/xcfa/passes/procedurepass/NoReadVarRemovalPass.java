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

import com.google.common.collect.Sets;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.frontend.transformation.ArchitectureConfig;
import hu.bme.mit.theta.xcfa.model.XcfaEdge;
import hu.bme.mit.theta.xcfa.model.XcfaLabel;
import hu.bme.mit.theta.xcfa.model.XcfaProcedure;
import hu.bme.mit.theta.xcfa.model.utils.LabelUtils;

import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

public class NoReadVarRemovalPass extends ProcedurePass {
	@Override
	public XcfaProcedure.Builder run(XcfaProcedure.Builder builder) {
		if(ArchitectureConfig.multiThreading) return builder;

		Set<VarDecl<?>> assignedToVars = new LinkedHashSet<>();
		Set<VarDecl<?>> usedUpVars = new LinkedHashSet<>();

		for (XcfaEdge edge : builder.getEdges()) {
			for (XcfaLabel label : edge.getLabels()) {
				LabelUtils.getAssortedVars(label, assignedToVars, usedUpVars);
			}
		}
		final Set<VarDecl<?>> toRemove = Sets.difference(assignedToVars, usedUpVars);
		for (XcfaEdge edge : new ArrayList<>(builder.getEdges())) {
			List<XcfaLabel> newLabels = new ArrayList<>();
			for (XcfaLabel label : edge.getLabels()) {
				if(LabelUtils.getVars(label).stream().noneMatch(toRemove::contains)) {
					newLabels.add(label);
				}
			}
			if(newLabels.size() != edge.getLabels().size()) {
				final XcfaEdge newEdge = edge.withLabels(newLabels);
				builder.removeEdge(edge);
				builder.addEdge(newEdge);
			}
		}
		return builder;
	}

	@Override
	public boolean isPostInlining() {
		return true;
	}
}
