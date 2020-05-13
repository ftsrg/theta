package hu.bme.mit.theta.xcfa.alt.algorithm;

public class Config {
    public boolean rememberTraces = false;
    public boolean debug = false;
    /**
     * Optimize when there is a process with only local transitions,
     *  at least one of them being local.
     */
    public boolean optimizeLocals = false;

}
