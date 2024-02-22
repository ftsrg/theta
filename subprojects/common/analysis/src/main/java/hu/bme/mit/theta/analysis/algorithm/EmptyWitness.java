package hu.bme.mit.theta.analysis.algorithm;

public class EmptyWitness implements Witness {

    private final static EmptyWitness empty = new EmptyWitness();

    private EmptyWitness() {
    }

    public static EmptyWitness getInstance() {
        return empty;
    }

}
