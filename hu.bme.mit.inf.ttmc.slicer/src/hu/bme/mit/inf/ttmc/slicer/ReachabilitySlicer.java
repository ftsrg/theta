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
		/*
		 * This slicing algorithm builds a Program Dependence Graph from the given CFG.
		 * All nodes reachable from the criteria node are considered needed.
		 *
		 * TODO: Several unneeded nodes are present in the slice because of the way the data dependences are computed.
		 * Let's assume S --> P --> Q is a sequential path in the CFG and S, P are assignments on variable i. If Q uses variable i
		 * for reading Q flow depends on S and P, thus both are present in the slice.
		 * However because P overrides the value set by S, so S could be sliced out.
		 */
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
