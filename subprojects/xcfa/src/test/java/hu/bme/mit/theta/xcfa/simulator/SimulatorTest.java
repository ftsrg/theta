package hu.bme.mit.theta.xcfa.simulator;

import hu.bme.mit.theta.xcfa.XCFA;
import hu.bme.mit.theta.xcfa.dsl.XcfaDslManager;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameter;
import org.junit.runners.Parameterized.Parameters;

import java.io.File;
import java.io.FileInputStream;
import java.io.IOException;
import java.io.InputStream;
import java.util.Arrays;
import java.util.Collection;

@RunWith(Parameterized.class)
public class SimulatorTest {

    @Parameter()
    public String filepath;

    @Parameters()
    public static Collection<Object[]> data() {
        return Arrays.asList(
                new Object[]{"src/test/resources/fibonacci.xcfa"},
                new Object[]{"src/test/resources/simple-test.xcfa"}
            );
    }

    @Test
    public void test() throws IOException {
        //final InputStream inputStream = new FileInputStream("/home/rl/cpp/theta-xcfa/theta/out/test/theta/peterson.xcfa");
        final InputStream inputStream = new FileInputStream(filepath);
        XCFA xcfa = XcfaDslManager.createXcfa(inputStream);
        new Simulator(xcfa);
    }
}
