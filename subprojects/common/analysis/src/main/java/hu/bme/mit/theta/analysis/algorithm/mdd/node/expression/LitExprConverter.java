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
import hu.bme.mit.theta.core.type.Expr;
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
import java.util.function.IntPredicate;

/** Util class for converting between integers and {@link LitExpr} */
public class LitExprConverter {

    private static int cnt = 0;
    private static final BiMap<Object, Integer> objToInt = HashBiMap.create();

    // symbolic mode: int and bitvector keys are interned like arrays, so terms over symbols can be
    // keys too
    private static boolean symbolic = false;

    public static void setSymbolic(boolean symbolic) {
        LitExprConverter.symbolic = symbolic;
    }

    public static boolean isSymbolic() {
        return symbolic;
    }

    private static int intern(Object obj) {
        final Integer known = objToInt.get(obj);
        if (known != null) return known;
        final int id = cnt++;
        objToInt.put(obj, id);
        return id;
    }

    private static boolean interned(Type type) {
        return type instanceof ArrayType<?, ?>
                || type instanceof FpType
                || type instanceof RatType
                || (symbolic && (type instanceof IntType || type instanceof BvType));
    }

    /** The key of a literal or, in symbolic mode, of a term over symbols. */
    public static int toInt(Expr<?> expr) {
        if (expr instanceof LitExpr<?> litExpr) return toInt(litExpr);
        Preconditions.checkState(symbolic, "Only literals can be keys outside symbolic mode");
        return intern(expr);
    }

    /** The literal or, in symbolic mode, the term a key stands for. */
    public static Expr<?> toExpr(int integer, Type type) {
        if (symbolic && interned(type)) {
            final Object obj = objToInt.inverse().get(integer);
            return obj == null ? new InvalidLitExpr<>(type) : (Expr<?>) obj;
        }
        return toLitExpr(integer, type);
    }

    /** A literal whose key is not used yet, for a decl a model leaves free. */
    public static LitExpr<?> unusedValue(IntPredicate used, Type type, int fallback) {
        if (!symbolic || !(type instanceof IntType || type instanceof BvType)) {
            return toLitExpr(fallback, type);
        }
        for (int value = 0; ; value++) {
            final LitExpr<?> lit =
                    type instanceof IntType
                            ? IntLitExpr.of(BigInteger.valueOf(value))
                            : BvUtils.bigIntegerToNeutralBvLitExpr(
                                    BigInteger.valueOf(value), ((BvType) type).getSize());
            if (!used.test(toInt(lit))) return lit;
        }
    }

    public static int toInt(LitExpr<?> litExpr) {
        if (symbolic && interned(litExpr.getType())) {
            return intern(litExpr);
        }
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
        if (litExpr instanceof ArrayLitExpr<?, ?>
                || litExpr instanceof FpLitExpr
                || litExpr instanceof RatLitExpr) {
            return intern(litExpr);
        }
        if (litExpr instanceof EnumLitExpr) {
            return ((EnumLitExpr) litExpr).getType().getIntValue((EnumLitExpr) litExpr);
        }
        throw new UnsupportedOperationException("Unsupported type");
    }

    public static LitExpr<?> toLitExpr(int integer, Type type) {
        if (symbolic && interned(type)) {
            final Object obj = objToInt.inverse().get(integer);
            return obj instanceof LitExpr<?> lit ? lit : new InvalidLitExpr<>(type);
        }
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
