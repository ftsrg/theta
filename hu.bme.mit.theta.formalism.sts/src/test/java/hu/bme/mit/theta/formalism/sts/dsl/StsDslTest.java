package hu.bme.mit.theta.formalism.sts.dsl;

import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.InputStream;

import org.junit.Test;

import hu.bme.mit.theta.formalism.sts.STS;

public class StsDslTest {

	@Test
	public void testReadersWriters() throws FileNotFoundException, IOException {
		final InputStream inputStream = StsDslTest.class.getResourceAsStream("/readerswriters.system");
		final StsSpec spec = StsDslManager.createStsSpec(inputStream);
		final STS sts = spec.createProp("safe");
		System.out.println(sts);
	}

	@Test
	public void testSimple() throws FileNotFoundException, IOException {
		final InputStream inputStream = StsDslTest.class.getResourceAsStream("/simple1.system");
		final StsSpec spec = StsDslManager.createStsSpec(inputStream);
		final STS sts = spec.createProp("safe");
		System.out.println(sts);
	}

}
