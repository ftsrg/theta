package hu.bme.mit.theta.frontend.petrinet.analysis;

import hu.bme.mit.delta.java.mdd.JavaMddFactory;
import hu.bme.mit.delta.java.mdd.MddGraph;
import hu.bme.mit.delta.java.mdd.MddSignature;
import hu.bme.mit.delta.java.mdd.MddVariableOrder;
import hu.bme.mit.delta.mdd.LatticeDefinition;
import hu.bme.mit.delta.mdd.MddVariableDescriptor;
import org.junit.Before;

public final class RelationalProductTest {
	private static final int[] tupleSignature     = new int[]{0, 0, 0};
	
	private MddGraph<Boolean> graph;
	private MddVariableOrder  order;
	private MddSignature      signature;
	
	@Before
	public void prepare() {
		System.out.println("Preparing...");
		graph = JavaMddFactory.getDefault().createMddGraph(LatticeDefinition.forSets());
		order = JavaMddFactory.getDefault().createMddVariableOrder(graph);
		for (int i = 0; i < tupleSignature.length; i++) {
			order.createOnTop(MddVariableDescriptor.create("x" + i, tupleSignature[tupleSignature.length - i - 1]));
		}
		signature = order.getDefaultSetSignature();
	}
}
