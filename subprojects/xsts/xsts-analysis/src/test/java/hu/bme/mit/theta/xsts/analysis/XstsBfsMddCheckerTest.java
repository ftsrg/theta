package hu.bme.mit.theta.xsts.analysis;

import hu.bme.mit.theta.analysis.algorithm.mdd.MddChecker.IterationStrategy;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;

@RunWith(value = org.junit.runners.Parameterized.class)
public class XstsBfsMddCheckerTest {

    @Parameterized.Parameter(value = 0)
    public String filePath;

    @Parameterized.Parameter(value = 1)
    public String propPath;

    @Parameterized.Parameter(value = 2)
    public boolean safe;

    @Parameterized.Parameters(name = "{index}: {0}, {1}, {2}")
    public static java.util.Collection<Object[]> data() {
        return XstsMddCheckerTest.data();
    }

    @Test
    public void testBfs() throws Exception {
        XstsMddCheckerTest.runTestWithIterationStrategy(filePath, propPath, safe, IterationStrategy.BFS);
    }

}
