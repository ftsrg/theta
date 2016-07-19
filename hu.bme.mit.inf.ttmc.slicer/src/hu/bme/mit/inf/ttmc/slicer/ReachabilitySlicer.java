package hu.bme.mit.inf.ttmc.slicer;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Function;
import java.util.function.Predicate;
import java.util.stream.Collectors;

import hu.bme.mit.inf.ttmc.formalism.common.stmt.AssertStmt;
import hu.bme.mit.inf.ttmc.slicer.cfg.CFG;
import hu.bme.mit.inf.ttmc.slicer.cfg.CFGNode;
import hu.bme.mit.inf.ttmc.slicer.cfg.StmtCFGNode;
import hu.bme.mit.inf.ttmc.slicer.dependence.PDG;
import hu.bme.mit.inf.ttmc.slicer.dependence.PDGNode;
import hu.bme.mit.inf.ttmc.slicer.graph.GraphAlgorithm;

public class ReachabilitySlicer implements CFGSlicer {

	public static final Predicate<CFGNode> SLICE_ON_ASSERTS = (CFGNode s) -> {
		return s instanceof StmtCFGNode && ((StmtCFGNode) s).getStmt() instanceof AssertStmt;
	};

	public List<CFG> allSlices(CFG input, Predicate<CFGNode> pred) {
		List<CFGNode> criteria = input.nodes().stream().filter(pred).collect(Collectors.toList());
		List<CFG> output = new ArrayList<>();

		for (CFGNode crit : criteria) {
			output.add(this.slice(input, crit));
		}

		return output;
	}

	@Override
	public CFG slice(CFG input, CFGNode criteria) {
		/*
		 * This slicing algorithm builds a Program Dependence Graph from the given CFG.
		 * All nodes reachable from the criteria node in the PDG are considered needed.
		 */
		Map<CFGNode, CFGNode> cfgMap = new HashMap<>();

		CFG output = input.copy(cfgMap);

		PDG pdg = PDG.fromCFG(output);

		List<PDGNode> visited = GraphAlgorithm.reverseDFS(pdg.findCFGNode(cfgMap.get(criteria)));

		for (CFGNode node : output.nodes()) {
			if (!visited.contains(pdg.findCFGNode(node))) {
				node.remove();
			}
		}

		cfgMap.get(criteria).addChild(output.getExit());

		return output;
	}

}
