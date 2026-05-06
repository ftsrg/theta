package hu.bme.mit.theta.xta.utils;

public class CTLOperatorNotSupportedException extends RuntimeException {
    public CTLOperatorNotSupportedException(final String operator) {
        super(operator + " is not supported");
    }
}
