package hu.bme.mit.theta.xsts;

import java.io.IOException;
import java.util.Arrays;
import java.util.Collection;

import org.junit.Assert;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameter;
import org.junit.runners.Parameterized.Parameters;

@RunWith(Parameterized.class)
public class Test1 {

	@Parameter(value = 0)
	public String path;

	@Parameter(value = 1)
	public int sizeOld;

	@Parameter(value = 2)
	public int sizeNew;

	@Parameters
	public static Collection<Object[]> data() {
		return Arrays.asList(new Object[][]{

				{"coi1.aag", 8, 3},

				{"coi2.aag", 5, 3},

				{"simple.aag", 6, 5},

				{"simple2.aag", 6, 5},

				{"simple3.aag", 7, 6},

		});
	}

	@Test
	public void test() throws IOException {
	}

}
