package hu.bme.mit.theta.analysis;

public class EmptyCex implements Cex {

    private final static EmptyCex empty = new EmptyCex();

    private EmptyCex() {
    }

    public static EmptyCex getInstance() {
        return empty;
    }

    @Override
    public int length() {
        return 0;
    }
}
