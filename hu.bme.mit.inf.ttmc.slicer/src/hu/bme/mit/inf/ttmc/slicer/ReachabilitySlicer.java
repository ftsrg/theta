package hu.bme.mit.inf.ttmc.slicer;

import java.util.HashMap;
import java.util.Map;
import java.util.Set;

import hu.bme.mit.inf.ttmc.slicer.cfg.CFG;
import hu.bme.mit.inf.ttmc.slicer.cfg.CFGNode;
import hu.bme.mit.inf.ttmc.slicer.graph.GraphAlgorithm;
import hu.bme.mit.inf.ttmc.slicer.pdg.PDG;
import hu.bme.mit.inf.ttmc.slicer.pdg.PDGNode;

public class ReachabilitySlicer implements CFGSlicer {

	@Override
	public CFG slice(CFG input, CFGNode criteria) {
		Map<CFGNode, CFGNode> cfgMap = new HashMap<>();

		CFG output = input.copy(cfgMap);
		PDG pdg = PDG.fromCFG(output);

		Set<PDGNode> visited = GraphAlgorithm.reverseDFS(pdg.findCFGNode(cfgMap.get(criteria)));

		for (CFGNode node : output.nodes()) {
			if (!visited.contains(pdg.findCFGNode(node))) {
				node.remove();
			}
		}

		cfgMap.get(criteria).addChild(output.getExit());

		return output;
	}

}
