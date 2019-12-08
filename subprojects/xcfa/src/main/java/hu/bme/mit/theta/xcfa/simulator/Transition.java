package hu.bme.mit.theta.xcfa.simulator;

public interface Transition {
    void step();
    boolean enabled(RuntimeState state);
}
