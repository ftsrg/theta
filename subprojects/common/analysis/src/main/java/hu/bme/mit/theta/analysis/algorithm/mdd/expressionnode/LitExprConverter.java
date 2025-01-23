/*
 *  Copyright 2025 Budapest University of Technology and Economics
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
package hu.bme.mit.theta.analysis.algorithm.mdd.expressionnode;

import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool;

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
import hu.bme.mit.theta.core.utils.BvUtils;
import java.math.BigInteger;

/** Util class for converting between integers and {@link LitExpr} */
public class LitExprConverter {

    private static int cnt = 0;
    private static final BiMap<Object, Integer> objToInt = HashBiMap.create();

    public static int toInt(LitExpr<?> litExpr) {
        if (litExpr instanceof IntLitExpr) {
            return ((IntLitExpr) litExpr).getValue().intValue();
        }
        if (litExpr instanceof BoolLitExpr) {
            return ((BoolLitExpr) litExpr).getValue() ? 1 : 0;
        }
        if (litExpr instanceof BvLitExpr bvLitExpr) {
            var ret = BvUtils.neutralBvLitExprToBigInteger(bvLitExpr).intValue();
            return ret;
        }
        if (litExpr instanceof ArrayLitExpr<?, ?> || litExpr instanceof FpLitExpr) {
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
            return IntLitExpr.of(BigInteger.valueOf(integer));
        }
        if (type instanceof BoolType) {
            if (integer > 1 || integer < 0) {
                return new InvalidLitExpr<>(Bool());
            }
            return BoolLitExpr.of(integer != 0);
        }
        if (type instanceof BvType) {
            return BvUtils.bigIntegerToNeutralBvLitExpr(
                    BigInteger.valueOf(integer), ((BvType) type).getSize());
        }
        if (type instanceof ArrayType<?, ?> || type instanceof FpType) {
            return (LitExpr<?>) objToInt.inverse().get(integer);
        }
        if (type instanceof EnumType) {
            return ((EnumType) type).litFromIntValue(integer);
        }
        throw new UnsupportedOperationException("Unsupported type");
    }
}
