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

package hu.bme.mit.theta.cat.models;

import hu.bme.mit.theta.cat.solver.MemoryModel;
import hu.bme.mit.theta.cat.solver.MemoryModelBuilder;
import hu.bme.mit.theta.cat.solver.RuleDerivation;

public class CoherenceMemory extends MemoryModel {
	@Override
	public void applyRules(MemoryModelBuilder memoryModelBuilder) {
		super.applyRules(memoryModelBuilder);

		memoryModelBuilder.addRule(new RuleDerivation.Union("coherence",
				new RuleDerivation.Element("po", 2),
				new RuleDerivation.Union("coherence1",
						new RuleDerivation.Element("co", 2),
						new RuleDerivation.Union("coherence2",
								new RuleDerivation.Element("rf", 2),
								new RuleDerivation.Element("fr", 2)))));

		memoryModelBuilder.assertAcyclic("coherence");
	}
}
