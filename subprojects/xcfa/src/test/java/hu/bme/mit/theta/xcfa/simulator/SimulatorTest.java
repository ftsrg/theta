package hu.bme.mit.theta.xcfa.simulator;

import hu.bme.mit.theta.xcfa.XCFA;
import hu.bme.mit.theta.xcfa.dsl.XcfaDslManager;
import org.junit.Test;
import org.junit.runners.Parameterized.Parameter;
import org.junit.runners.Parameterized.Parameters;

import java.io.FileInputStream;
import java.io.IOException;
import java.io.InputStream;
import java.util.Arrays;
import java.util.Collection;

public class SimulatorTest {

    @Parameter(0)
    public String filepath;

    @Parameters()
    public static Collection<Object[]> data() {
        return Arrays.asList(new Object[][]{
                {"/peterson.xcfa"}
        });
    }

    @Test
    public void test() throws IOException {
        //final InputStream inputStream = new FileInputStream("/home/rl/cpp/theta-xcfa/theta/out/test/theta/peterson.xcfa");
        final InputStream inputStream = new FileInputStream("/home/rl/valami.xcfa");
        XCFA xcfa = XcfaDslManager.createXcfa(inputStream);
        new Simulator(xcfa);
    }
}
