package hu.bme.mit.theta.formalism.tcfa.dsl;

import static hu.bme.mit.theta.core.expr.impl.Exprs.Int;
import static java.util.Arrays.asList;

import java.io.FileNotFoundException;
import java.io.IOException;

import org.junit.Test;

import hu.bme.mit.theta.formalism.tcfa.TCFA;
import hu.bme.mit.theta.formalism.tcfa.TcfaPrinter;
import hu.bme.mit.theta.formalism.tcfa.dsl.TcfaDslManager;
import hu.bme.mit.theta.formalism.tcfa.dsl.TcfaSpec;

public class TcfaDslTests {

	@Test
	public void testFischer() throws FileNotFoundException, IOException {
		final TcfaSpec spec = TcfaDslManager.parse("src/test/resources/fischer.tcfa", asList(Int(1), Int(2)));
		final TCFA fischer = spec.getTcfa("fischers");
		System.out.println(TcfaPrinter.toGraphvizString(fischer));
	}

	@Test
	public void testProsigma() throws FileNotFoundException, IOException {
		final TcfaSpec spec = TcfaDslManager.parse("src/test/resources/prosigma.tcfa", asList(Int(3), Int(7)));
		final TCFA field = spec.getTcfa("prosigma");
		System.out.println(TcfaPrinter.toGraphvizString(field));
	}

}
