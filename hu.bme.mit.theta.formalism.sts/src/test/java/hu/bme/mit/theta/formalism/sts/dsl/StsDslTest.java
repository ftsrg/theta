package hu.bme.mit.theta.formalism.sts.dsl;

import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.InputStream;
import java.util.Arrays;
import java.util.Collection;

import org.junit.Assert;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameter;
import org.junit.runners.Parameterized.Parameters;

import hu.bme.mit.theta.formalism.sts.STS;

@RunWith(Parameterized.class)
public class StsDslTest {

	@Parameters
	public static Collection<Object[]> data() {
		return Arrays.asList(new Object[][] {

				{ "/readerswriters.system", "safe", 3 },

				{ "/simple1.system", "safe", 2 }

		});
	}

	@Parameter(0)
	public String filepath;

	@Parameter(1)
	public String propertyName;

	@Parameter(2)
	public int varCount;

	@Test
	public void test() throws FileNotFoundException, IOException {
		final InputStream inputStream = StsDslTest.class.getResourceAsStream(filepath);
		final StsSpec spec = StsDslManager.createStsSpec(inputStream);
		final STS sts = spec.createProp(propertyName);
		Assert.assertEquals(varCount, sts.getVars().size());
	}

}
