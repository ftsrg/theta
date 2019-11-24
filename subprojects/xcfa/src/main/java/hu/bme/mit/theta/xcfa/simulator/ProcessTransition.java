package hu.bme.mit.theta.xcfa.simulator;

abstract public class ProcessTransition implements Transition{

    protected ProcessState processState;

    public ProcessTransition(ProcessState p) {
        processState = p;
    }

}
