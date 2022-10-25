package hu.bme.mit.theta.xta.utils;

public class MixedDataTimeNotSupportedException extends RuntimeException {
    public MixedDataTimeNotSupportedException(final String guard) {
        super("Mixing data and clock variables inside one guard is not supported: " + guard);
    }
}
