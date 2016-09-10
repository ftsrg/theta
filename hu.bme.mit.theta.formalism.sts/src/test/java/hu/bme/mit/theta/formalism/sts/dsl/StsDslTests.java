package hu.bme.mit.theta.formalism.sts.dsl;

import static java.util.Collections.emptyList;

import java.io.FileNotFoundException;
import java.io.IOException;

import org.junit.Test;

import hu.bme.mit.theta.formalism.sts.STS;
import hu.bme.mit.theta.formalism.sts.dsl.StsDslManager;
import hu.bme.mit.theta.formalism.sts.dsl.impl.StsSpec;

public class StsDslTests {

	@Test
	public void testFischer() throws FileNotFoundException, IOException {
		final StsSpec spec = StsDslManager.parse("src/test/resources/readerswriters.system", emptyList());
		final STS sts = spec.getSts("s");
		System.out.println(sts);
	}

	@Test
	public void testProsigma() throws FileNotFoundException, IOException {
		final StsSpec spec = StsDslManager.parse("src/test/resources/simple1.system", emptyList());
		final STS sts = spec.getSts("safe");
		System.out.println(sts);
	}

}
