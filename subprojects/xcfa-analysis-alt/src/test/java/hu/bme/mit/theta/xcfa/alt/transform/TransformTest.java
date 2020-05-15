package hu.bme.mit.theta.xcfa.alt.transform;

import hu.bme.mit.theta.xcfa.XCFA;
import hu.bme.mit.theta.xcfa.alt.algorithm.ExplicitChecker;
import hu.bme.mit.theta.xcfa.alt.algorithm.XcfaChecker;
import hu.bme.mit.theta.xcfa.dsl.XcfaDslManager;
import org.junit.Test;

import java.io.IOException;
import java.io.InputStream;

public class TransformTest {

    @Test
    public void simpleTransformationTest() throws IOException {
        final InputStream inputStream = getClass().getResourceAsStream("/functions-global-local.xcfa");
        XCFA xcfa = XcfaDslManager.createXcfa(inputStream);

        xcfa = new DefaultTransformation(xcfa).build();
        var checker = ExplicitChecker.createChecker(xcfa, XcfaChecker.getSimpleExplicit().build());
        assert checker.check().isSafe();
    }
}
