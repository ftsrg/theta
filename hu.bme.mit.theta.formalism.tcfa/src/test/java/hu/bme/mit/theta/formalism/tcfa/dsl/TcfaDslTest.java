package hu.bme.mit.theta.formalism.tcfa.dsl;

import org.junit.Test;

import hu.bme.mit.theta.common.visualization.GraphvizWriter;
import hu.bme.mit.theta.formalism.tcfa.TCFA;
import hu.bme.mit.theta.formalism.tcfa.instances.TcfaModels;
import hu.bme.mit.theta.formalism.tcfa.utils.TcfaVisualizer;

public class TcfaDslTest {

	@Test
	public void testFischer() {
		final TCFA fischer = TcfaModels.fischer(2, 1, 2);
		System.out.println(new GraphvizWriter().writeString(TcfaVisualizer.visualize(fischer)));
	}

	@Test
	public void testProsigma() {
		final TCFA prosigma = TcfaModels.prosigma(3, 7);
		System.out.println(new GraphvizWriter().writeString(TcfaVisualizer.visualize(prosigma)));
	}

}
