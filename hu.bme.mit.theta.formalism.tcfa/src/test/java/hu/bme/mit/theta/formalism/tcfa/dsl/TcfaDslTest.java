package hu.bme.mit.theta.formalism.tcfa.dsl;

import org.junit.Test;

import hu.bme.mit.theta.common.visualization.GraphvizWriter;
import hu.bme.mit.theta.formalism.tcfa.TCFA;
import hu.bme.mit.theta.formalism.tcfa.instances.TcfaModels;
import hu.bme.mit.theta.formalism.tcfa.utils.TcfaVisualizer;

public class TcfaDslTest {

	@Test
	public void testProsigma() {
		final TCFA tcfa = TcfaModels.prosigma(3, 7);
		System.out.println(new GraphvizWriter().writeString(TcfaVisualizer.visualize(tcfa)));
	}

	@Test
	public void testFischer() {
		final TCFA tcfa = TcfaModels.fischer(2, 1);
		System.out.println(new GraphvizWriter().writeString(TcfaVisualizer.visualize(tcfa)));
	}

	@Test
	public void testCritRegion() {
		final TCFA tcfa = TcfaModels.critRegion(2, 10, 20);
		System.out.println(new GraphvizWriter().writeString(TcfaVisualizer.visualize(tcfa)));
	}

	@Test
	public void testLynch() {
		final TCFA tcfa = TcfaModels.lynch(2, 16);
		System.out.println(new GraphvizWriter().writeString(TcfaVisualizer.visualize(tcfa)));
	}

	@Test
	public void testFddi() {
		final TCFA tcfa = TcfaModels.fddi(2, 50 * 2, 20);
		System.out.println(new GraphvizWriter().writeString(TcfaVisualizer.visualize(tcfa)));
	}

}
