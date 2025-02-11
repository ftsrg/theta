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
package hu.bme.mit.theta.core.utils;

import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Not;

import hu.bme.mit.theta.common.DispatchTable;
import hu.bme.mit.theta.core.type.BinaryExpr;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.MultiaryExpr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.anytype.IteExpr;
import hu.bme.mit.theta.core.type.anytype.RefExpr;
import hu.bme.mit.theta.core.type.arraytype.ArrayReadExpr;
import hu.bme.mit.theta.core.type.arraytype.ArrayType;
import hu.bme.mit.theta.core.type.arraytype.ArrayWriteExpr;
import hu.bme.mit.theta.core.type.booltype.AndExpr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.type.booltype.IffExpr;
import hu.bme.mit.theta.core.type.booltype.ImplyExpr;
import hu.bme.mit.theta.core.type.booltype.NotExpr;
import hu.bme.mit.theta.core.type.booltype.OrExpr;
import hu.bme.mit.theta.core.type.booltype.XorExpr;
import hu.bme.mit.theta.core.type.inttype.IntAddExpr;
import hu.bme.mit.theta.core.type.inttype.IntDivExpr;
import hu.bme.mit.theta.core.type.inttype.IntEqExpr;
import hu.bme.mit.theta.core.type.inttype.IntExprs;
import hu.bme.mit.theta.core.type.inttype.IntGeqExpr;
import hu.bme.mit.theta.core.type.inttype.IntGtExpr;
import hu.bme.mit.theta.core.type.inttype.IntLeqExpr;
import hu.bme.mit.theta.core.type.inttype.IntLtExpr;
import hu.bme.mit.theta.core.type.inttype.IntModExpr;
import hu.bme.mit.theta.core.type.inttype.IntMulExpr;
import hu.bme.mit.theta.core.type.inttype.IntNegExpr;
import hu.bme.mit.theta.core.type.inttype.IntNeqExpr;
import hu.bme.mit.theta.core.type.inttype.IntPosExpr;
import hu.bme.mit.theta.core.type.inttype.IntSubExpr;
import hu.bme.mit.theta.core.type.inttype.IntToRatExpr;
import hu.bme.mit.theta.core.type.inttype.IntType;
import hu.bme.mit.theta.core.type.rattype.RatAddExpr;
import hu.bme.mit.theta.core.type.rattype.RatDivExpr;
import hu.bme.mit.theta.core.type.rattype.RatEqExpr;
import hu.bme.mit.theta.core.type.rattype.RatExprs;
import hu.bme.mit.theta.core.type.rattype.RatGeqExpr;
import hu.bme.mit.theta.core.type.rattype.RatGtExpr;
import hu.bme.mit.theta.core.type.rattype.RatLeqExpr;
import hu.bme.mit.theta.core.type.rattype.RatLtExpr;
import hu.bme.mit.theta.core.type.rattype.RatMulExpr;
import hu.bme.mit.theta.core.type.rattype.RatNegExpr;
import hu.bme.mit.theta.core.type.rattype.RatNeqExpr;
import hu.bme.mit.theta.core.type.rattype.RatPosExpr;
import hu.bme.mit.theta.core.type.rattype.RatSubExpr;
import hu.bme.mit.theta.core.type.rattype.RatToIntExpr;
import hu.bme.mit.theta.core.type.rattype.RatType;
import java.util.Comparator;
import java.util.List;
import java.util.stream.Collectors;

public final class ExprCanonizer {

    private static final DispatchTable<Expr<?>> TABLE =
            DispatchTable.<Expr<?>>builder()

                    // Boolean

                    .addCase(NotExpr.class, ExprCanonizer::canonizeNot)
                    .addCase(ImplyExpr.class, ExprCanonizer::canonizeImply)
                    .addCase(IffExpr.class, ExprCanonizer::canonizeIff)
                    .addCase(XorExpr.class, ExprCanonizer::canonizeXor)
                    .addCase(AndExpr.class, ExprCanonizer::canonizeAnd)
                    .addCase(OrExpr.class, ExprCanonizer::canonizeOr)

                    // Rational

                    .addCase(RatAddExpr.class, ExprCanonizer::canonizeRatAdd)
                    .addCase(RatSubExpr.class, ExprCanonizer::canonizeRatSub)
                    .addCase(RatPosExpr.class, ExprCanonizer::canonizeRatPos)
                    .addCase(RatNegExpr.class, ExprCanonizer::canonizeRatNeg)
                    .addCase(RatMulExpr.class, ExprCanonizer::canonizeRatMul)
                    .addCase(RatDivExpr.class, ExprCanonizer::canonizeRatDiv)
                    .addCase(RatEqExpr.class, ExprCanonizer::canonizeRatEq)
                    .addCase(RatNeqExpr.class, ExprCanonizer::canonizeRatNeq)
                    .addCase(RatGeqExpr.class, ExprCanonizer::canonizeRatGeq)
                    .addCase(RatGtExpr.class, ExprCanonizer::canonizeRatGt)
                    .addCase(RatLeqExpr.class, ExprCanonizer::canonizeRatLeq)
                    .addCase(RatLtExpr.class, ExprCanonizer::canonizeRatLt)
                    .addCase(RatToIntExpr.class, ExprCanonizer::canonizeRatToInt)

                    // Integer

                    .addCase(IntToRatExpr.class, ExprCanonizer::canonizeIntToRat)
                    .addCase(IntAddExpr.class, ExprCanonizer::canonizeIntAdd)
                    .addCase(IntSubExpr.class, ExprCanonizer::canonizeIntSub)
                    .addCase(IntPosExpr.class, ExprCanonizer::canonizeIntPos)
                    .addCase(IntNegExpr.class, ExprCanonizer::canonizeIntNeg)
                    .addCase(IntMulExpr.class, ExprCanonizer::canonizeIntMul)
                    .addCase(IntDivExpr.class, ExprCanonizer::canonizeIntDiv)
                    .addCase(IntModExpr.class, ExprCanonizer::canonizeMod)
                    .addCase(IntEqExpr.class, ExprCanonizer::canonizeIntEq)
                    .addCase(IntNeqExpr.class, ExprCanonizer::canonizeIntNeq)
                    .addCase(IntGeqExpr.class, ExprCanonizer::canonizeIntGeq)
                    .addCase(IntGtExpr.class, ExprCanonizer::canonizeIntGt)
                    .addCase(IntLeqExpr.class, ExprCanonizer::canonizeIntLeq)
                    .addCase(IntLtExpr.class, ExprCanonizer::canonizeIntLt)

                    // Array

                    .addCase(ArrayReadExpr.class, ExprCanonizer::canonizeArrayRead)
                    .addCase(ArrayWriteExpr.class, ExprCanonizer::canonizeArrayWrite)

                    // General

                    .addCase(RefExpr.class, ExprCanonizer::canonizeRef)
                    .addCase(IteExpr.class, ExprCanonizer::canonizeIte)

                    // Default

                    .addDefault(
                            (o) -> {
                                final Expr<?> expr = (Expr<?>) o;
                                return expr.map(e -> canonize(e));
                            })
                    .build();

    private ExprCanonizer() {}

    @SuppressWarnings("unchecked")
    public static <T extends Type> Expr<T> canonize(final Expr<T> expr) {
        return (Expr<T>) TABLE.dispatch(expr);
    }

    /*
     * General
     */

    private static Expr<?> canonizeRef(final RefExpr<?> expr) {
        return expr;
    }

    private static Expr<?> canonizeIte(final IteExpr<?> expr) {
        return canonizeGenericIte(expr);
    }

    // TODO Eliminate helper method once the Java compiler is able to handle
    // this kind of type inference
    private static <ExprType extends Type> Expr<ExprType> canonizeGenericIte(
            final IteExpr<ExprType> expr) {
        final Expr<BoolType> cond = canonize(expr.getCond());
        final Expr<ExprType> then = canonize(expr.getThen());
        final Expr<ExprType> elze = canonize(expr.getElse());

        return expr.with(cond, then, elze);
    }

    private static Expr<?> canonizeArrayRead(final ArrayReadExpr<?, ?> expr) {
        return canonizeGenericArrayRead(expr);
    }

    private static <IT extends Type, ET extends Type> Expr<ET> canonizeGenericArrayRead(
            final ArrayReadExpr<IT, ET> expr) {
        Expr<ArrayType<IT, ET>> arr = canonize(expr.getArray());
        Expr<IT> index = canonize(expr.getIndex());

        return expr.with(arr, index);
    }

    private static Expr<?> canonizeArrayWrite(final ArrayWriteExpr<?, ?> expr) {
        return canonizeGenericArrayWrite(expr);
    }

    private static <IT extends Type, ET extends Type>
            Expr<ArrayType<IT, ET>> canonizeGenericArrayWrite(final ArrayWriteExpr<IT, ET> expr) {
        Expr<ArrayType<IT, ET>> arr = canonize(expr.getArray());
        Expr<IT> index = canonize(expr.getIndex());
        Expr<ET> elem = canonize(expr.getElem());

        return expr.with(arr, index, elem);
    }

    /*
     * Booleans
     */

    private static Expr<BoolType> canonizeNot(final NotExpr expr) {
        final Expr<BoolType> op = canonize(expr.getOp());

        return expr.with(op);
    }

    private static Expr<BoolType> canonizeImply(final ImplyExpr expr) {
        final Expr<BoolType> leftOp = canonize(expr.getLeftOp());
        final Expr<BoolType> rightOp = canonize(expr.getRightOp());

        return expr.with(leftOp, rightOp);
    }

    private static <OpType extends Type, ExprType extends Type>
            Expr<ExprType> canonizeGenericCommutativeBinaryExpr(
                    final BinaryExpr<OpType, ExprType> expr) {
        final Expr<OpType> leftOp = canonize(expr.getLeftOp());
        final Expr<OpType> rightOp = canonize(expr.getRightOp());

        final int leftHashCode = leftOp.hashCode();
        final int rightHashCode = rightOp.hashCode();

        if (rightHashCode < leftHashCode) {
            return expr.with(rightOp, leftOp);
        } else {
            return expr.with(leftOp, rightOp);
        }
    }

    private static Expr<BoolType> canonizeIff(final IffExpr expr) {
        return canonizeGenericCommutativeBinaryExpr(expr);
    }

    private static Expr<BoolType> canonizeXor(final XorExpr expr) {
        return canonizeGenericCommutativeBinaryExpr(expr);
    }

    private static <OpType extends Type, ExprType extends Type>
            Expr<ExprType> canonizeGenericCommutativeMultiaryExpr(
                    final MultiaryExpr<OpType, ExprType> expr) {
        final List<Expr<OpType>> orderedCanonizedOps =
                expr.getOps().stream()
                        .map(ExprCanonizer::canonize)
                        .sorted(Comparator.comparingInt(Object::hashCode))
                        .collect(Collectors.toList());

        return expr.withOps(orderedCanonizedOps);
    }

    private static Expr<BoolType> canonizeAnd(final AndExpr expr) {
        return canonizeGenericCommutativeMultiaryExpr(expr);
    }

    private static Expr<BoolType> canonizeOr(final OrExpr expr) {
        return canonizeGenericCommutativeMultiaryExpr(expr);
    }

    /*
     * Rationals
     */

    private static Expr<RatType> canonizeRatAdd(final RatAddExpr expr) {
        return canonizeGenericCommutativeMultiaryExpr(expr);
    }

    private static Expr<RatType> canonizeRatSub(final RatSubExpr expr) {
        final Expr<RatType> leftOp = canonize(expr.getLeftOp());
        final Expr<RatType> rightOp = canonize(expr.getRightOp());

        return expr.with(leftOp, rightOp);
    }

    private static Expr<RatType> canonizeRatPos(final RatPosExpr expr) {
        return canonize(expr.getOp());
    }

    private static Expr<RatType> canonizeRatNeg(final RatNegExpr expr) {
        final Expr<RatType> op = canonize(expr.getOp());

        return expr.with(op);
    }

    private static Expr<RatType> canonizeRatMul(final RatMulExpr expr) {
        return canonizeGenericCommutativeMultiaryExpr(expr);
    }

    private static Expr<RatType> canonizeRatDiv(final RatDivExpr expr) {
        final Expr<RatType> leftOp = canonize(expr.getLeftOp());
        final Expr<RatType> rightOp = canonize(expr.getRightOp());

        return expr.with(leftOp, rightOp);
    }

    private static Expr<BoolType> canonizeRatEq(final RatEqExpr expr) {
        return canonizeGenericCommutativeBinaryExpr(expr);
    }

    private static Expr<BoolType> canonizeRatNeq(final RatNeqExpr expr) {
        final Expr<BoolType> notEq = Not(RatExprs.Eq(expr.getLeftOp(), expr.getRightOp()));
        return canonize(notEq);
    }

    private static Expr<BoolType> canonizeRatGeq(final RatGeqExpr expr) {
        final Expr<BoolType> notLt = Not(RatExprs.Lt(expr.getLeftOp(), expr.getRightOp()));
        return canonize(notLt);
    }

    private static Expr<BoolType> canonizeRatGt(final RatGtExpr expr) {
        final Expr<RatType> leftOp = canonize(expr.getLeftOp());
        final Expr<RatType> rightOp = canonize(expr.getRightOp());

        return RatLtExpr.of(rightOp, leftOp);
    }

    private static Expr<BoolType> canonizeRatLeq(final RatLeqExpr expr) {
        final Expr<BoolType> notGt = Not(RatExprs.Gt(expr.getLeftOp(), expr.getRightOp()));
        return canonize(notGt);
    }

    private static Expr<BoolType> canonizeRatLt(final RatLtExpr expr) {
        final Expr<RatType> leftOp = canonize(expr.getLeftOp());
        final Expr<RatType> rightOp = canonize(expr.getRightOp());

        return expr.with(leftOp, rightOp);
    }

    private static Expr<IntType> canonizeRatToInt(final RatToIntExpr expr) {
        final Expr<RatType> op = canonize(expr.getOp());

        return expr.with(op);
    }

    /*
     * Integers
     */

    private static Expr<RatType> canonizeIntToRat(final IntToRatExpr expr) {
        final Expr<IntType> op = canonize(expr.getOp());

        return expr.with(op);
    }

    private static Expr<IntType> canonizeIntAdd(final IntAddExpr expr) {
        return canonizeGenericCommutativeMultiaryExpr(expr);
    }

    private static Expr<IntType> canonizeIntSub(final IntSubExpr expr) {
        final Expr<IntType> leftOp = canonize(expr.getLeftOp());
        final Expr<IntType> rightOp = canonize(expr.getRightOp());

        return expr.with(leftOp, rightOp);
    }

    private static Expr<IntType> canonizeIntPos(final IntPosExpr expr) {
        return canonize(expr.getOp());
    }

    private static Expr<IntType> canonizeIntNeg(final IntNegExpr expr) {
        final Expr<IntType> op = canonize(expr.getOp());

        return expr.with(op);
    }

    private static Expr<IntType> canonizeIntMul(final IntMulExpr expr) {
        return canonizeGenericCommutativeMultiaryExpr(expr);
    }

    private static Expr<IntType> canonizeIntDiv(final IntDivExpr expr) {
        final Expr<IntType> leftOp = canonize(expr.getLeftOp());
        final Expr<IntType> rightOp = canonize(expr.getRightOp());

        return expr.with(leftOp, rightOp);
    }

    private static Expr<IntType> canonizeMod(final IntModExpr expr) {
        final Expr<IntType> leftOp = canonize(expr.getLeftOp());
        final Expr<IntType> rightOp = canonize(expr.getRightOp());

        return expr.with(leftOp, rightOp);
    }

    private static Expr<BoolType> canonizeIntEq(final IntEqExpr expr) {
        return canonizeGenericCommutativeBinaryExpr(expr);
    }

    private static Expr<BoolType> canonizeIntNeq(final IntNeqExpr expr) {
        final Expr<BoolType> notEq = Not(IntExprs.Eq(expr.getLeftOp(), expr.getRightOp()));
        return canonize(notEq);
    }

    private static Expr<BoolType> canonizeIntGeq(final IntGeqExpr expr) {
        final Expr<BoolType> notLt = Not(IntExprs.Lt(expr.getLeftOp(), expr.getRightOp()));
        return canonize(notLt);
    }

    private static Expr<BoolType> canonizeIntGt(final IntGtExpr expr) {
        final Expr<IntType> leftOp = canonize(expr.getLeftOp());
        final Expr<IntType> rightOp = canonize(expr.getRightOp());

        return IntLtExpr.of(rightOp, leftOp);
    }

    private static Expr<BoolType> canonizeIntLeq(final IntLeqExpr expr) {
        final Expr<BoolType> notGt = Not(IntExprs.Gt(expr.getLeftOp(), expr.getRightOp()));
        return canonize(notGt);
    }

    private static Expr<BoolType> canonizeIntLt(final IntLtExpr expr) {
        final Expr<IntType> leftOp = canonize(expr.getLeftOp());
        final Expr<IntType> rightOp = canonize(expr.getRightOp());

        return expr.with(leftOp, rightOp);
    }
}
