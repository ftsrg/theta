package hu.bme.mit.theta.core.utils;

import hu.bme.mit.theta.core.type.bvtype.BvLitExpr;

import java.math.BigInteger;

import static hu.bme.mit.theta.core.type.bvtype.BvExprs.Bv;

public final class BvUtils {
    private BvUtils() {

    }

    public static BigInteger bvLitExprToBigInteger(final BvLitExpr expr) {
        BigInteger integer = BigInteger.ZERO;

        for(int i = 0; i < expr.getType().getSize(); i++) {
            if(expr.getValue()[expr.getType().getSize() - 1 - i]) {
                integer = integer.setBit(i);
            }
        }

        if(expr.getType().isSigned() && expr.getValue()[0]) {
            integer = integer.subtract(BigInteger.TWO.multiply(BigInteger.valueOf(expr.getType().getSize()-1)));
        }

        return integer;
    }

    public static BvLitExpr bigIntegerToBvLitExpr(BigInteger integer, final int size, final boolean isSigned) {
        if(isSigned && integer.compareTo(BigInteger.ZERO) < 0) {
            integer = integer.add(BigInteger.TWO.multiply(BigInteger.valueOf(size-1)));
        }

        boolean[] values = new boolean[size];
        for(int i = 0; i < size; i++) {
            values[size - 1 - i] = integer.testBit(i);
        }

        return Bv(values, isSigned);
    }
}
