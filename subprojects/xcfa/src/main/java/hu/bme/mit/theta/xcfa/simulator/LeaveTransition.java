package hu.bme.mit.theta.xcfa.simulator;

public class LeaveTransition extends ProcessTransition {

    public LeaveTransition(ProcessState p) {
        super(p);
    }

    @Override
    public void step() {
        processState.callStack.peek().end();
    }

    @Override
    public boolean enabled(RuntimeState state) {
        return true;
    }
}
