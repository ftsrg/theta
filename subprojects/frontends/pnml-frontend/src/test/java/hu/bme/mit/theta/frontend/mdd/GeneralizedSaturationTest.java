package hu.bme.mit.theta.frontend.mdd;

import hu.bme.mit.delta.java.mdd.GraphvizSerializer;
import hu.bme.mit.delta.java.mdd.JavaMddFactory;
import hu.bme.mit.delta.java.mdd.MddHandle;
import hu.bme.mit.delta.java.mdd.MddVariableOrder;
import hu.bme.mit.delta.mdd.LatticeDefinition;
import hu.bme.mit.delta.mdd.MddInterpreter;
import hu.bme.mit.delta.mdd.MddVariableDescriptor;
import hu.bme.mit.theta.frontend.mdd.mdd.GeneralizedSaturationProvider;
import hu.bme.mit.theta.frontend.mdd.mdd.RelationalProductProvider;
import hu.bme.mit.theta.frontend.mdd.ptnet.PtNetSystem;
import hu.bme.mit.theta.frontend.mdd.ptnet.VariableOrderingFactory;
import hu.bme.mit.theta.frontend.petrinet.model.PetriNet;
import hu.bme.mit.theta.frontend.petrinet.model.Place;
import hu.bme.mit.theta.frontend.petrinet.pnml.PetriNetParser;
import org.junit.Test;

import java.awt.*;
import java.awt.datatransfer.Clipboard;
import java.awt.datatransfer.StringSelection;
import java.io.File;
import java.util.List;

import static org.junit.Assert.assertEquals;

public final class GeneralizedSaturationTest {
	public static String reverseString(String str){
		StringBuilder sb=new StringBuilder(str);
		sb.reverse();
		return sb.toString();
	}
	
	@Test
	public void testGS() throws Exception {
		final File pnmlFile = new File(getClass().getResource(TestData.MODELPATH).toURI());
		final List<PetriNet> petriNets = PetriNetParser.loadPnml(pnmlFile).parsePTNet();
		
		assertEquals(1, petriNets.size());
		
		final List<Place> ordering = VariableOrderingFactory.fromFile(getClass().getResource(TestData.ORDERINGPATH).toURI().getPath(), petriNets.get(0));
		// 	ordering = new ArrayList<>(petriNets.get(0).getPlaces());
		// ordering.sort((p1, p2) -> String.CASE_INSENSITIVE_ORDER.compare(reverseString(p1.getId()),
		// 	reverseString(p2.getId())));
		// ordering.sort((p1, p2) -> String.CASE_INSENSITIVE_ORDER.compare(p1.getId(),
		// 	p2.getId()));
		
		PtNetSystem system = new PtNetSystem(petriNets.get(0), ordering);
		
		System.out.println(system.printDependencyMatrixCsv());
		
		//new BufferedReader(new InputStreamReader(System.in)).readLine();
		
		MddVariableOrder variableOrder =
			JavaMddFactory.getDefault().createMddVariableOrder(LatticeDefinition.forSets());
		for (Place p : ordering) {
			variableOrder.createOnTop(MddVariableDescriptor.create(p));
		}
		
		GeneralizedSaturationProvider gs = new GeneralizedSaturationProvider(variableOrder,
			new RelationalProductProvider(variableOrder));
		
		final MddHandle stateSpace = gs.compute(system.getInitializer(),
			system.getTransitions(),
			variableOrder.getDefaultSetSignature().getTopVariableHandle()
		);
		
		String dot = GraphvizSerializer.serialize(stateSpace);
		System.out.println(dot);
		
		StringSelection stringSelection = new StringSelection(dot);
		Clipboard clipboard = Toolkit.getDefaultToolkit().getSystemClipboard();
		clipboard.setContents(stringSelection, null);
		
		final Long stateSpaceSize = MddInterpreter.calculateNonzeroCount(stateSpace);
		assertEquals(TestData.STATESPACESIZE, stateSpaceSize.longValue());
		System.out.println("Size of state space: " + stateSpaceSize);
	}
}
