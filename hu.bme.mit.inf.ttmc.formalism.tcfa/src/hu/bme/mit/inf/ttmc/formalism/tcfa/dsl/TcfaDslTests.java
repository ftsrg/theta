package hu.bme.mit.inf.ttmc.formalism.tcfa.dsl;

import java.io.FileNotFoundException;
import java.io.IOException;

import org.junit.Test;

import hu.bme.mit.inf.ttmc.formalism.tcfa.TCFA;
import hu.bme.mit.inf.ttmc.formalism.tcfa.TCFAPrinter;
import hu.bme.mit.inf.ttmc.formalism.tcfa.dsl.impl.TcfaSpec;

public class TcfaDslTests {

	@Test
	public void testFischer() throws FileNotFoundException, IOException {
		final TcfaSpec spec = TcfaDslManager.parse("instances/fischer.tcfa");
		final TCFA fischer = spec.getTcfa("fischer");
		System.out.println(TCFAPrinter.toGraphvizSting(fischer));
	}

	@Test
	public void testProsigma() throws FileNotFoundException, IOException {
		final TcfaSpec spec = TcfaDslManager.parse("instances/prosigma.tcfa");
		final TCFA field = spec.getTcfa("field");
		System.out.println(TCFAPrinter.toGraphvizSting(field));
	}

}
