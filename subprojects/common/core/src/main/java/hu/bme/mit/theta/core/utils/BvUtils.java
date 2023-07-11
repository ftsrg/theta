/*
 *  Copyright 2023 Budapest University of Technology and Economics
 *
 *  Licensed under the Apache License, Version 2.0 (the "License");
 *  you may not use this file except in compliance with the License.
 *  You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 *  Unless required by applicable law or agreed to in writing, software
 *  distributed under the License is distributed on an "AS IS" BASIS,
 *  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *  See the License for the specific language governing permissions and
 *  limitations under the License.
 */

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

        for (int i = 0; i < expr.getType().getSize(); i++) {
            if (expr.getValue()[expr.getType().getSize() - 1 - i]) {
                integer = integer.setBit(i);
            }
        }

        return integer;
    }

    public static BigInteger signedBvLitExprToBigInteger(final BvLitExpr expr) {
        BigInteger integer = unsignedBvLitExprToBigInteger(expr);

        if (expr.getValue()[0]) {
            integer = integer.subtract(BigInteger.TWO.pow(expr.getType().getSize()));
        }

        return integer;
    }

    public static BvLitExpr bigIntegerToNeutralBvLitExpr(BigInteger integer, final int size) {
        boolean[] values = getBvRepresentation(integer, size);
        return Bv(values);
    }

    public static BvLitExpr bigIntegerToUnsignedBvLitExpr(BigInteger integer, final int size) {
        boolean[] values = getBvRepresentation(integer, size);
        return Bv(values, false);
    }

    private static boolean[] getBvRepresentation(BigInteger integer, int size) {
        boolean[] values = new boolean[size];
        for (int i = 0; i < size; i++) {
            values[size - 1 - i] = integer.testBit(i);
        }
        return values;
    }

    public static BvLitExpr bigIntegerToSignedBvLitExpr(BigInteger integer, final int size) {
        if (integer.compareTo(BigInteger.ZERO) < 0) {
            integer = integer.add(BigInteger.TWO.pow(size));
        }
        boolean[] values = getBvRepresentation(integer, size);
        return Bv(values, true);
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
        while (integer.compareTo(BigInteger.ZERO) < 0) {
            integer = integer.add(BigInteger.TWO.pow(size));
        }

        while (integer.compareTo(BigInteger.TWO.pow(size)) >= 0) {
            integer = integer.subtract(BigInteger.TWO.pow(size));
        }

        return integer;
    }
}
