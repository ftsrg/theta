package hu.bme.mit.theta.formalism.cfa.dsl;

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

import hu.bme.mit.theta.formalism.cfa.CFA;

@RunWith(Parameterized.class)
public final class CfaDslManagerTest {

	@Parameters()
	public static Collection<Object[]> data() {
		return Arrays.asList(new Object[][] {

				{ "/locking.cfa", 3, 6, 7, 8 },

				{ "/counter5_true.cfa", 1, 6, 6, 6 }

		});
	}

	@Parameter(0)
	public String filepath;

	@Parameter(1)
	public int varCount;

	@Parameter(2)
	public int locCount;

	@Parameter(3)
	public int edgeCount;

	@Parameter(4)
	public int stmtCount;

	@Test
	public void test() throws FileNotFoundException, IOException {
		final InputStream inputStream = getClass().getResourceAsStream(filepath);
		final CFA cfa = CfaDslManager.createCfa(inputStream);
		Assert.assertEquals(varCount, cfa.getVars().size());
		Assert.assertEquals(locCount, cfa.getLocs().size());
		Assert.assertEquals(edgeCount, cfa.getEdges().size());
		Assert.assertEquals(stmtCount, cfa.getEdges().stream().flatMap(e -> e.getStmts().stream()).count());
	}

}
