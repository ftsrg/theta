package hu.bme.mit.inf.theta.frontend.transform;

import java.util.List;
import java.util.stream.Collectors;

import hu.bme.mit.inf.theta.frontend.dependency.UseDefineChain;
import hu.bme.mit.inf.theta.frontend.ir.BasicBlock;
import hu.bme.mit.inf.theta.frontend.ir.Function;
import hu.bme.mit.inf.theta.frontend.ir.node.AssignNode;

public class DeadInstructionElimination implements FunctionTransformer {

	@Override
	public void transform(Function function) {
		UseDefineChain ud = UseDefineChain.buildChain(function);

		for (BasicBlock block : function.getBlocksDFS()) {
			List<AssignNode<?, ?>> nodes = block.getNodes()
				.stream()
				.filter(node -> node instanceof AssignNode<?, ?>)
				.map(node -> (AssignNode<?, ?>) node)
				.collect(Collectors.toList());

			for (AssignNode<?, ?> node : nodes) {
				if (ud.getLocalReachableUses(node).size() == 0) { // This value is not used anywhere
					int idx = block.getNodeIndex(node);
					block.removeNode(idx);
				}
			}
		}
	}

	@Override
	public String getTransformationName() {
		return "DeadInstructionElimination";
	}

}
