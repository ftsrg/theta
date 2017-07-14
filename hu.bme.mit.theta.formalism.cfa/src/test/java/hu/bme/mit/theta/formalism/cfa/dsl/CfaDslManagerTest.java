package hu.bme.mit.theta.formalism.cfa.dsl;

import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.InputStream;
import java.util.Arrays;
import java.util.Collection;

import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameter;
import org.junit.runners.Parameterized.Parameters;

import hu.bme.mit.theta.common.visualization.writer.GraphvizWriter;
import hu.bme.mit.theta.formalism.cfa.CFA;
import hu.bme.mit.theta.formalism.cfa.utils.CfaVisualizer;

@RunWith(Parameterized.class)
public final class CfaDslManagerTest {

	@Parameters(name = "{0}")
	public static Collection<Object[]> data() {
		return Arrays.asList(new Object[][] {

				{ "/locking.cfa" }

		});
	}

	@Parameter(0)
	public String filepath;

	@Test
	public void test() throws FileNotFoundException, IOException {
		final InputStream inputStream = getClass().getResourceAsStream(filepath);
		final CFA cfa = CfaDslManager.createCfa(inputStream);
		System.out.println(cfa.getVars());
		System.out.println(new GraphvizWriter().writeString(CfaVisualizer.visualize(cfa)));
	}

}
