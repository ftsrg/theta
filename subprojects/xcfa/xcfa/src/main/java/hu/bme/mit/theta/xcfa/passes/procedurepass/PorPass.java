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

package hu.bme.mit.theta.xcfa.passes.procedurepass;

import hu.bme.mit.theta.frontend.transformation.ArchitectureConfig;
import hu.bme.mit.theta.xcfa.model.XcfaEdge;
import hu.bme.mit.theta.xcfa.model.XcfaLabel;
import hu.bme.mit.theta.xcfa.model.XcfaLocation;
import hu.bme.mit.theta.xcfa.model.XcfaProcedure;
import hu.bme.mit.theta.xcfa.model.utils.LabelUtils;

import java.util.ArrayList;
import java.util.List;

public class PorPass extends ProcedurePass {
	@Override
	public XcfaProcedure.Builder run(XcfaProcedure.Builder builder) {
		if (!ArchitectureConfig.multiThreading) return builder;
		for (XcfaEdge edge : new ArrayList<>(builder.getEdges())) {
			List<XcfaLabel> newLabels = new ArrayList<>();
			boolean removed = false;
			XcfaLocation source = edge.getSource();
			for (XcfaLabel label : edge.getLabels()) {
				if (LabelUtils.isNotLocal(label, builder.getLocalVars())) {
					if (!removed) {
						builder.removeEdge(edge);
						removed = true;
					}
					if (newLabels.size() > 0) {
						XcfaLocation tmp = XcfaLocation.create("tmp" + XcfaLocation.uniqeCounter());
						builder.addLoc(tmp);
						builder.addEdge(edge.withSource(source).withLabels(newLabels).withTarget(tmp));
						source = tmp;
						newLabels.clear();
					}
					XcfaLocation tmp = XcfaLocation.create("tmp" + XcfaLocation.uniqeCounter());
					builder.addLoc(tmp);
					builder.addEdge(edge.withSource(source).withLabels(List.of(label)).withTarget(tmp));
					source = tmp;
				} else {
					newLabels.add(label);
				}
			}
			if (removed) {
				builder.addEdge(edge.withSource(source).withLabels(newLabels).withTarget(edge.getTarget()));
			}
		}
		return builder;
	}

	@Override
	public boolean isPostInlining() {
		return true;
	}
}