package hu.bme.mit.theta.xcfa.alt.algorithm;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.algorithm.SafetyResult;
import org.junit.Assert;

public class Helper {
    public static void checkResult(SafetyResult<? extends State, ? extends Action> result, boolean shouldWork) {
        System.err.println("Safety result: " + (result.isSafe() ? "Safe" : "Unsafe"));
        if (!result.isSafe()) {
            System.err.println("Trace:");
            for (Action t : result.asUnsafe().getTrace().getActions()) {
                System.err.println(t);
            }
        }
        Assert.assertFalse("Error reached, but it shouldn't have been. Error: %s" + result, shouldWork && !result.isSafe());
        Assert.assertFalse("Error or deadlock is not reached, but it should have been.", !shouldWork && result.isSafe());
    }
}
