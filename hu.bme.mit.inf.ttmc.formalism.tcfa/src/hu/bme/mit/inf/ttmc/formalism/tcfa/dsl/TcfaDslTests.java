package hu.bme.mit.inf.ttmc.formalism.tcfa.dsl;

import static hu.bme.mit.inf.ttmc.core.expr.impl.Exprs.Int;
import static java.util.Arrays.asList;

import java.io.FileNotFoundException;
import java.io.IOException;

import org.junit.Test;

import hu.bme.mit.inf.ttmc.formalism.tcfa.TCFA;
import hu.bme.mit.inf.ttmc.formalism.tcfa.TCFAPrinter;

public class TcfaDslTests {

	@Test
	public void testFischer() throws FileNotFoundException, IOException {
		final TcfaSpec spec = TcfaDslManager.parse("instances/fischer.tcfa", asList(Int(1), Int(2)));
		final TCFA fischer = spec.getTcfa("fischers");
		System.out.println(TCFAPrinter.toGraphvizString(fischer));
	}

	@Test
	public void testProsigma() throws FileNotFoundException, IOException {
		final TcfaSpec spec = TcfaDslManager.parse("instances/prosigma.tcfa", asList(Int(3), Int(7)));
		final TCFA field = spec.getTcfa("prosigma");
		System.out.println(TCFAPrinter.toGraphvizString(field));
	}

}
