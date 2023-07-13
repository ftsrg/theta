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

import hu.bme.mit.theta.core.decl.Decl;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.arraytype.ArrayExprs;
import hu.bme.mit.theta.core.type.arraytype.ArrayType;
import hu.bme.mit.theta.core.type.booltype.BoolExprs;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.type.bvtype.BvExprs;
import hu.bme.mit.theta.core.type.bvtype.BvType;
import hu.bme.mit.theta.core.type.fptype.FpType;
import hu.bme.mit.theta.core.type.inttype.IntExprs;
import hu.bme.mit.theta.core.type.inttype.IntType;
import hu.bme.mit.theta.core.type.rattype.RatExprs;
import hu.bme.mit.theta.core.type.rattype.RatType;
import org.kframework.mpfr.BigFloat;

import java.math.BigInteger;
import java.util.Iterator;
import java.util.List;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;

/**
 * Utility functions related to types.
 */
public final class TypeUtils {

    private TypeUtils() {
    }

    /**
     * Cast a declaration to a given type.
     *
     * @param decl Original declaration
     * @param type Type
     * @return Casted declaration
     */
    public static <T extends Type> Decl<T> cast(final Decl<?> decl, final T type) {
        checkNotNull(decl);
        checkNotNull(type);

        if (decl.getType().equals(type)) {
            @SuppressWarnings("unchecked") final Decl<T> result = (Decl<T>) decl;
            return result;
        } else {
            throw new ClassCastException(
                    "The type of declaration " + decl + " is not of type " + type);
        }
    }

    /**
     * Cast a variable declaration to a given type.
     *
     * @param decl Original declaration
     * @param type Type
     * @return Casted declaration
     */
    public static <T extends Type> VarDecl<T> cast(final VarDecl<?> decl, final T type) {
        checkNotNull(decl);
        checkNotNull(type);

        if (decl.getType().equals(type)) {
            @SuppressWarnings("unchecked") final VarDecl<T> result = (VarDecl<T>) decl;
            return result;
        } else {
            throw new ClassCastException(
                    "The type of declaration " + decl + " is not of type " + type);
        }
    }

    /**
     * Cast an expression to a given type.
     *
     * @param expr Original expression
     * @param type Type
     * @return Casted expression
     */
    public static <T extends Type> Expr<T> cast(final Expr<?> expr, final T type) {
        checkNotNull(expr);
        checkNotNull(type);

        if (expr.getType().equals(type)) {
            @SuppressWarnings("unchecked") final Expr<T> result = (Expr<T>) expr;
            return result;
        } else {
            throw new ClassCastException(
                    "The type of expression " + expr + " is not of type " + type);
        }
    }

    /**
     * Cast an expression to bitvector type.
     *
     * @param expr Original expression
     * @return Casted expression
     */
    public static Expr<BvType> castBv(final Expr<?> expr) {
        checkNotNull(expr);

        if (expr.getType() instanceof BvType) {
            @SuppressWarnings("unchecked") final Expr<BvType> result = (Expr<BvType>) expr;
            return result;
        } else {
            throw new ClassCastException(
                    "The type of expression " + expr + " is not of type BvType");
        }
    }

    /**
     * Cast an expression to floating point type.
     *
     * @param expr Original expression
     * @return Casted expression
     */
    public static Expr<FpType> castFp(final Expr<?> expr) {
        checkNotNull(expr);

        if (expr.getType() instanceof FpType) {
            @SuppressWarnings("unchecked") final Expr<FpType> result = (Expr<FpType>) expr;
            return result;
        } else {
            throw new ClassCastException(
                    "The type of expression " + expr + " is not of type FpType");
        }
    }

    /**
     * Check if all the types of the operands equal
     *
     * @param ops The expressions
     */
    public static void checkAllTypesEqual(final Iterable<? extends Expr<?>> ops) {
        checkNotNull(ops);

        final Iterator<? extends Expr<?>> iterator = ops.iterator();
        checkArgument(iterator.hasNext(), "There must be at least one element");

        final Expr<?> first = iterator.next();
        while (iterator.hasNext()) {
            final Expr<?> nth = iterator.next();
            checkArgument(first.getType().equals(nth.getType()), "All types must equal");
        }
    }

    /**
     * Check if all the types of the operands equal
     *
     * @param op The expression
     */
    public static void checkAllTypesEqual(final Expr<?> op) {
        checkNotNull(op);
    }

    /**
     * Check if all the types of the operands equal
     *
     * @param op1 The expression
     * @param op2 The expression
     */
    public static void checkAllTypesEqual(final Expr<?> op1, final Expr<?> op2) {
        checkNotNull(op1);
        checkNotNull(op2);
        checkArgument(op1.getType().equals(op2.getType()), "All types must equal");
    }

    public static <T extends Type> LitExpr<T> getDefaultValue(final T type) {
        if (type instanceof BoolType) {
            return (LitExpr<T>) cast(BoolExprs.False(), type);
        } else if (type instanceof IntType) {
            return (LitExpr<T>) cast(IntExprs.Int(0), type);
        } else if (type instanceof RatType) {
            return (LitExpr<T>) cast(RatExprs.Rat(0, 1), type);
        } else if (type instanceof BvType) {
            return (LitExpr<T>) cast(BvUtils.bigIntegerToNeutralBvLitExpr(BigInteger.ZERO, ((BvType) type).getSize()), type);
        } else if (type instanceof FpType) {
            return (LitExpr<T>) cast(FpUtils.bigFloatToFpLitExpr(BigFloat.zero(((FpType) type).getSignificand()), (FpType) type), type);
        } else {
            throw new AssertionError();
        }
    }

}
