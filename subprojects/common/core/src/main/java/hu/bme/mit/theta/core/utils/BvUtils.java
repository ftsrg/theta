package hu.bme.mit.theta.core.utils;

import hu.bme.mit.theta.core.type.bvtype.BvLitExpr;

import java.math.BigInteger;

import static hu.bme.mit.theta.core.type.bvtype.BvExprs.Bv;

public final class BvUtils {
    private BvUtils() {

    }

    public static BigInteger neutralBvLitExprToBigInteger(final BvLitExpr expr) {
        return unsignedBvLitExprToBigInteger(expr);
    }

    public static BigInteger unsignedBvLitExprToBigInteger(final BvLitExpr expr) {
        BigInteger integer = BigInteger.ZERO;

        for(int i = 0; i < expr.getType().getSize(); i++) {
            if(expr.getValue()[expr.getType().getSize() - 1 - i]) {
                integer = integer.setBit(i);
            }
        }

        return integer;
    }

    public static BigInteger signedBvLitExprToBigInteger(final BvLitExpr expr) {
        BigInteger integer = unsignedBvLitExprToBigInteger(expr);

        if(expr.getValue()[0]) {
            integer = integer.subtract(BigInteger.TWO.pow(expr.getType().getSize()));
        }

        return integer;
    }

    public static BvLitExpr bigIntegerToNeutralBvLitExpr(BigInteger integer, final int size) {
        return bigIntegerToUnsignedBvLitExpr(integer, size);
    }

    public static BvLitExpr bigIntegerToUnsignedBvLitExpr(BigInteger integer, final int size) {

        boolean[] values = new boolean[size];
        for(int i = 0; i < size; i++) {
            values[size - 1 - i] = integer.testBit(i);
        }

        return Bv(values);
    }

    public static BvLitExpr bigIntegerToSignedBvLitExpr(BigInteger integer, final int size) {
        if(integer.compareTo(BigInteger.ZERO) < 0) {
            integer = integer.add(BigInteger.TWO.pow(size));
        }

        return bigIntegerToUnsignedBvLitExpr(integer, size);
    }

    public static BigInteger fitBigIntegerIntoNeutralDomain(BigInteger integer, final int size) {
        return fitBigIntegerIntoUnsignedDomain(integer, size);
    }

    public static BigInteger fitBigIntegerIntoSignedDomain(BigInteger integer, final int size) {
        while (integer.compareTo(BigInteger.TWO.pow(size - 1).negate()) < 0) {
            integer = integer.add(BigInteger.TWO.pow(size));
        }

        while (integer.compareTo(BigInteger.TWO.pow(size - 1)) >= 0) {
            integer = integer.subtract(BigInteger.TWO.pow(size));
        }

        return integer;
    }

    public static BigInteger fitBigIntegerIntoUnsignedDomain(BigInteger integer, final int size) {
        while(integer.compareTo(BigInteger.ZERO) < 0) {
            integer = integer.add(BigInteger.TWO.pow(size));
        }

        while(integer.compareTo(BigInteger.TWO.pow(size)) >= 0) {
            integer = integer.subtract(BigInteger.TWO.pow(size));
        }

        return integer;
    }
}
