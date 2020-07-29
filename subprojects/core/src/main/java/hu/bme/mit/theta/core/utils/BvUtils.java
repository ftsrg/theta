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
            integer = integer.subtract(BigInteger.TWO.pow(expr.getType().getSize()));
        }

        return integer;
    }

    public static int bvLitExprToInt(final BvLitExpr expr) {
        return bvLitExprToBigInteger(expr).intValue();
    }

    public static BvLitExpr bigIntegerToBvLitExpr(BigInteger integer, final int size, final boolean isSigned) {
        if(isSigned && integer.compareTo(BigInteger.ZERO) < 0) {
            integer = integer.add(BigInteger.TWO.pow(size));
        }

        boolean[] values = new boolean[size];
        for(int i = 0; i < size; i++) {
            values[size - 1 - i] = integer.testBit(i);
        }

        return Bv(values, isSigned);
    }

    public static BvLitExpr intToBvLitExpr(final int integer, final int size, final boolean isSigned) {
        return bigIntegerToBvLitExpr(BigInteger.valueOf(integer), size, isSigned);
    }

    public static BvLitExpr uint32ToBvLitExpr(final int integer) {
        return intToBvLitExpr(integer, 32, false);
    }

    public static BvLitExpr sint32ToBvLitExpr(final int integer) {
        return intToBvLitExpr(integer, 32, true);
    }

    public static BvLitExpr uint16ToBvLitExpr(final int integer) {
        return intToBvLitExpr(integer, 16, false);
    }

    public static BvLitExpr sint16ToBvLitExpr(final int integer) {
        return intToBvLitExpr(integer, 16, true);
    }

    public static BigInteger fitBigIntegerIntoDomain(BigInteger integer, final int size, final boolean isSigned) {
        if(isSigned) {
            while(integer.compareTo(BigInteger.TWO.pow(size-1).negate()) < 0) {
                integer = integer.add(BigInteger.TWO.pow(size));
            }

            while(integer.compareTo(BigInteger.TWO.pow(size-1)) >= 0) {
                integer = integer.subtract(BigInteger.TWO.pow(size));
            }
        }
        else {
            while(integer.compareTo(BigInteger.ZERO) < 0) {
                integer = integer.add(BigInteger.TWO.pow(size));
            }

            while(integer.compareTo(BigInteger.TWO.pow(size)) >= 0) {
                integer = integer.subtract(BigInteger.TWO.pow(size));
            }
        }

        return integer;
    }
}
