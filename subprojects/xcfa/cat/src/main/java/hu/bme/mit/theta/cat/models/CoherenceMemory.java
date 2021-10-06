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
				new RuleDerivation.Union( "coherence1",
						new RuleDerivation.Element("co", 2),
						new RuleDerivation.Union("coherence2",
								new RuleDerivation.Element("rf", 2),
								new RuleDerivation.Element("fr", 2)))));

		memoryModelBuilder.assertAcyclic("coherence");
	}
}
