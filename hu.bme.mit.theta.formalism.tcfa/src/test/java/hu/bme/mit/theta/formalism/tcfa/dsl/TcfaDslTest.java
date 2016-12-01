package hu.bme.mit.theta.formalism.tcfa.dsl;

import static hu.bme.mit.theta.core.expr.impl.Exprs.Int;

import java.io.FileNotFoundException;
import java.io.IOException;

import org.junit.Test;

import hu.bme.mit.theta.common.visualization.YedWriter;
import hu.bme.mit.theta.formalism.tcfa.TCFA;
import hu.bme.mit.theta.formalism.tcfa.utils.TcfaVisualizer;

public class TcfaDslTest {

	@Test
	public void testFischer() throws FileNotFoundException, IOException {
		final TcfaSpec spec = TcfaDslManager.parse("src/test/resources/fischer.tcfa", Int(1), Int(2));
		final TCFA fischer = spec.getTcfa("fischers");
		System.out.println(new YedWriter().writeString(TcfaVisualizer.visualize(fischer)));
	}

	@Test
	public void testProsigma() throws FileNotFoundException, IOException {
		final TcfaSpec spec = TcfaDslManager.parse("src/test/resources/prosigma.tcfa", Int(3), Int(7));
		final TCFA field = spec.getTcfa("prosigma");
		System.out.println(new YedWriter().writeString(TcfaVisualizer.visualize(field)));
	}

}
