package hu.bme.mit.theta.xcfa.alt.algorithm;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.Trace;
import hu.bme.mit.theta.analysis.algorithm.SafetyResult;
import org.junit.Assert;

public class Helper {

    public static void printTrace(Trace<? extends State, ? extends Action> trace) {
        System.err.println("Trace:");
        for (Action t : trace.getActions()) {
            System.err.println(t);
        }
    }

    public static void checkResult(SafetyResult<? extends State, ? extends Action> result, boolean shouldWork) {
        System.err.println("Safety result: " + (result.isSafe() ? "Safe" : "Unsafe"));
        if (!result.isSafe()) {
            printTrace(result.asUnsafe().getTrace());
        }
        Assert.assertFalse(String.format("Error reached, but it shouldn't have been. Error: %s", result), shouldWork && !result.isSafe());
        Assert.assertFalse("Error or deadlock is not reached, but it should have been.", !shouldWork && result.isSafe());
    }
}
