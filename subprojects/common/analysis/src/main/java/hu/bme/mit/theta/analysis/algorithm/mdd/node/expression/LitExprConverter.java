/*
 *  Copyright 2026 Budapest University of Technology and Economics
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
package hu.bme.mit.theta.analysis.algorithm.mdd.node.expression;

import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool;

import com.google.common.base.Preconditions;
import com.google.common.collect.BiMap;
import com.google.common.collect.HashBiMap;
import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.anytype.InvalidLitExpr;
import hu.bme.mit.theta.core.type.arraytype.ArrayLitExpr;
import hu.bme.mit.theta.core.type.arraytype.ArrayType;
import hu.bme.mit.theta.core.type.booltype.BoolLitExpr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.type.bvtype.BvLitExpr;
import hu.bme.mit.theta.core.type.bvtype.BvType;
import hu.bme.mit.theta.core.type.enumtype.EnumLitExpr;
import hu.bme.mit.theta.core.type.enumtype.EnumType;
import hu.bme.mit.theta.core.type.fptype.FpLitExpr;
import hu.bme.mit.theta.core.type.fptype.FpType;
import hu.bme.mit.theta.core.type.inttype.IntLitExpr;
import hu.bme.mit.theta.core.type.inttype.IntType;
import hu.bme.mit.theta.core.type.rattype.RatLitExpr;
import hu.bme.mit.theta.core.type.rattype.RatType;
import hu.bme.mit.theta.core.utils.BvUtils;
import java.math.BigInteger;

/** Util class for converting between integers and {@link LitExpr} */
public class LitExprConverter {

    private static int cnt = 0;
    private static final BiMap<Object, Integer> objToInt = HashBiMap.create();

    private static final int WIDE_BAND_SIZE = 1 << 16;

    private static final int WIDE_BAND_END = Integer.MIN_VALUE + WIDE_BAND_SIZE;
    private static final BiMap<LitExpr<?>, Integer> wideToInt = HashBiMap.create();

    private static boolean isWideKey(int key) {
        return key < WIDE_BAND_END;
    }

    private static synchronized int wideKey(LitExpr<?> litExpr) {
        final Integer existing = wideToInt.get(litExpr);
        if (existing != null) {
            return existing;
        }
        Preconditions.checkState(wideToInt.size() < WIDE_BAND_SIZE, "Out of keys for wide values");
        final int key = Integer.MIN_VALUE + wideToInt.size();
        wideToInt.put(litExpr, key);
        return key;
    }

    private static synchronized LitExpr<?> wideLitExpr(int key) {
        return wideToInt.inverse().get(key);
    }

    public static boolean isWide(LitExpr<?> litExpr) {
        if (litExpr instanceof IntLitExpr intLitExpr) {
            return intLitExpr.getValue().bitLength() >= Integer.SIZE;
        }
        if (litExpr instanceof BvLitExpr bvLitExpr) {
            return bvLitExpr.getType().getSize() > Integer.SIZE
                    && BvUtils.neutralBvLitExprToBigInteger(bvLitExpr).bitLength() >= Integer.SIZE;
        }
        return false;
    }

    public static int toInt(LitExpr<?> litExpr) {
        if (litExpr instanceof IntLitExpr intLitExpr) {
            final BigInteger value = intLitExpr.getValue();
            if (value.bitLength() < Integer.SIZE && !isWideKey(value.intValue())) {
                return value.intValue();
            }
            return wideKey(intLitExpr);
        }
        if (litExpr instanceof BoolLitExpr) {
            return ((BoolLitExpr) litExpr).getValue() ? 1 : 0;
        }
        if (litExpr instanceof BvLitExpr bvLitExpr) {
            final BigInteger value = BvUtils.neutralBvLitExprToBigInteger(bvLitExpr);
            final int size = bvLitExpr.getType().getSize();
            if (size <= Integer.SIZE || value.bitLength() < Integer.SIZE) {
                return value.intValue();
            }
            return wideKey(BvUtils.bigIntegerToNeutralBvLitExpr(value, size));
        }
        if (litExpr instanceof ArrayLitExpr<?, ?>
                || litExpr instanceof FpLitExpr
                || litExpr instanceof RatLitExpr) {
            if (objToInt.get(litExpr) != null) {
                return objToInt.get(litExpr);
            }
            final int id = cnt++;
            objToInt.put(litExpr, id);
            return id;
        }
        if (litExpr instanceof EnumLitExpr) {
            return ((EnumLitExpr) litExpr).getType().getIntValue((EnumLitExpr) litExpr);
        }
        throw new UnsupportedOperationException("Unsupported type");
    }

    public static LitExpr<?> toLitExpr(int integer, Type type) {
        if (type instanceof IntType) {
            if (!isWideKey(integer)) return IntLitExpr.of(BigInteger.valueOf(integer));
            final LitExpr<?> wide = wideLitExpr(integer);
            return wide instanceof IntLitExpr ? wide : new InvalidLitExpr<>(type);
        }
        if (type instanceof BoolType) {
            if (integer > 1 || integer < 0) {
                return new InvalidLitExpr<>(Bool());
            }
            return BoolLitExpr.of(integer != 0);
        }
        if (type instanceof BvType bvType) {
            if (bvType.getSize() <= Integer.SIZE || integer >= 0) {
                return BvUtils.bigIntegerToNeutralBvLitExpr(
                        BigInteger.valueOf(integer), bvType.getSize());
            }
            final LitExpr<?> wide = isWideKey(integer) ? wideLitExpr(integer) : null;
            return wide instanceof BvLitExpr bv && bv.getType().getSize() == bvType.getSize()
                    ? wide
                    : new InvalidLitExpr<>(type);
        }
        if (type instanceof ArrayType<?, ?> || type instanceof FpType || type instanceof RatType) {
            if (!objToInt.inverse().containsKey(integer)) return new InvalidLitExpr<>(type);
            return (LitExpr<?>) objToInt.inverse().get(integer);
        }
        if (type instanceof EnumType) {
            return ((EnumType) type).litFromIntValue(integer);
        }
        throw new UnsupportedOperationException("Unsupported type");
    }
}
