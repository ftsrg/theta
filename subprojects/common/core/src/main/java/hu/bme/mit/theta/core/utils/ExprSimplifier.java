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

import hu.bme.mit.theta.common.DispatchTable2;
import hu.bme.mit.theta.common.Tuple2;
import hu.bme.mit.theta.common.Utils;
import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.anytype.IteExpr;
import hu.bme.mit.theta.core.type.anytype.RefExpr;
import hu.bme.mit.theta.core.type.arraytype.ArrayInitExpr;
import hu.bme.mit.theta.core.type.arraytype.ArrayReadExpr;
import hu.bme.mit.theta.core.type.arraytype.ArrayType;
import hu.bme.mit.theta.core.type.arraytype.ArrayWriteExpr;
import hu.bme.mit.theta.core.type.booltype.AndExpr;
import hu.bme.mit.theta.core.type.booltype.BoolLitExpr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.type.booltype.FalseExpr;
import hu.bme.mit.theta.core.type.booltype.IffExpr;
import hu.bme.mit.theta.core.type.booltype.ImplyExpr;
import hu.bme.mit.theta.core.type.booltype.NotExpr;
import hu.bme.mit.theta.core.type.booltype.OrExpr;
import hu.bme.mit.theta.core.type.booltype.TrueExpr;
import hu.bme.mit.theta.core.type.booltype.XorExpr;
import hu.bme.mit.theta.core.type.bvtype.BvAddExpr;
import hu.bme.mit.theta.core.type.bvtype.BvAndExpr;
import hu.bme.mit.theta.core.type.bvtype.BvArithShiftRightExpr;
import hu.bme.mit.theta.core.type.bvtype.BvConcatExpr;
import hu.bme.mit.theta.core.type.bvtype.BvEqExpr;
import hu.bme.mit.theta.core.type.bvtype.BvExtractExpr;
import hu.bme.mit.theta.core.type.bvtype.BvLitExpr;
import hu.bme.mit.theta.core.type.bvtype.BvLogicShiftRightExpr;
import hu.bme.mit.theta.core.type.bvtype.BvMulExpr;
import hu.bme.mit.theta.core.type.bvtype.BvNegExpr;
import hu.bme.mit.theta.core.type.bvtype.BvNeqExpr;
import hu.bme.mit.theta.core.type.bvtype.BvNotExpr;
import hu.bme.mit.theta.core.type.bvtype.BvOrExpr;
import hu.bme.mit.theta.core.type.bvtype.BvPosExpr;
import hu.bme.mit.theta.core.type.bvtype.BvRotateLeftExpr;
import hu.bme.mit.theta.core.type.bvtype.BvRotateRightExpr;
import hu.bme.mit.theta.core.type.bvtype.BvSDivExpr;
import hu.bme.mit.theta.core.type.bvtype.BvSExtExpr;
import hu.bme.mit.theta.core.type.bvtype.BvSGeqExpr;
import hu.bme.mit.theta.core.type.bvtype.BvSGtExpr;
import hu.bme.mit.theta.core.type.bvtype.BvSLeqExpr;
import hu.bme.mit.theta.core.type.bvtype.BvSLtExpr;
import hu.bme.mit.theta.core.type.bvtype.BvSModExpr;
import hu.bme.mit.theta.core.type.bvtype.BvSRemExpr;
import hu.bme.mit.theta.core.type.bvtype.BvShiftLeftExpr;
import hu.bme.mit.theta.core.type.bvtype.BvSubExpr;
import hu.bme.mit.theta.core.type.bvtype.BvType;
import hu.bme.mit.theta.core.type.bvtype.BvUDivExpr;
import hu.bme.mit.theta.core.type.bvtype.BvUGeqExpr;
import hu.bme.mit.theta.core.type.bvtype.BvUGtExpr;
import hu.bme.mit.theta.core.type.bvtype.BvULeqExpr;
import hu.bme.mit.theta.core.type.bvtype.BvULtExpr;
import hu.bme.mit.theta.core.type.bvtype.BvURemExpr;
import hu.bme.mit.theta.core.type.bvtype.BvXorExpr;
import hu.bme.mit.theta.core.type.bvtype.BvZExtExpr;
import hu.bme.mit.theta.core.type.fptype.FpAbsExpr;
import hu.bme.mit.theta.core.type.fptype.FpAddExpr;
import hu.bme.mit.theta.core.type.fptype.FpAssignExpr;
import hu.bme.mit.theta.core.type.fptype.FpDivExpr;
import hu.bme.mit.theta.core.type.fptype.FpEqExpr;
import hu.bme.mit.theta.core.type.fptype.FpFromBvExpr;
import hu.bme.mit.theta.core.type.fptype.FpGeqExpr;
import hu.bme.mit.theta.core.type.fptype.FpGtExpr;
import hu.bme.mit.theta.core.type.fptype.FpIsInfiniteExpr;
import hu.bme.mit.theta.core.type.fptype.FpIsNanExpr;
import hu.bme.mit.theta.core.type.fptype.FpLeqExpr;
import hu.bme.mit.theta.core.type.fptype.FpLitExpr;
import hu.bme.mit.theta.core.type.fptype.FpLtExpr;
import hu.bme.mit.theta.core.type.fptype.FpMaxExpr;
import hu.bme.mit.theta.core.type.fptype.FpMinExpr;
import hu.bme.mit.theta.core.type.fptype.FpMulExpr;
import hu.bme.mit.theta.core.type.fptype.FpNegExpr;
import hu.bme.mit.theta.core.type.fptype.FpNeqExpr;
import hu.bme.mit.theta.core.type.fptype.FpPosExpr;
import hu.bme.mit.theta.core.type.fptype.FpRoundToIntegralExpr;
import hu.bme.mit.theta.core.type.fptype.FpSqrtExpr;
import hu.bme.mit.theta.core.type.fptype.FpSubExpr;
import hu.bme.mit.theta.core.type.fptype.FpToBvExpr;
import hu.bme.mit.theta.core.type.fptype.FpToFpExpr;
import hu.bme.mit.theta.core.type.fptype.FpType;
import hu.bme.mit.theta.core.type.inttype.IntAddExpr;
import hu.bme.mit.theta.core.type.inttype.IntDivExpr;
import hu.bme.mit.theta.core.type.inttype.IntEqExpr;
import hu.bme.mit.theta.core.type.inttype.IntGeqExpr;
import hu.bme.mit.theta.core.type.inttype.IntGtExpr;
import hu.bme.mit.theta.core.type.inttype.IntLeqExpr;
import hu.bme.mit.theta.core.type.inttype.IntLitExpr;
import hu.bme.mit.theta.core.type.inttype.IntLtExpr;
import hu.bme.mit.theta.core.type.inttype.IntModExpr;
import hu.bme.mit.theta.core.type.inttype.IntMulExpr;
import hu.bme.mit.theta.core.type.inttype.IntNegExpr;
import hu.bme.mit.theta.core.type.inttype.IntNeqExpr;
import hu.bme.mit.theta.core.type.inttype.IntPosExpr;
import hu.bme.mit.theta.core.type.inttype.IntRemExpr;
import hu.bme.mit.theta.core.type.inttype.IntSubExpr;
import hu.bme.mit.theta.core.type.inttype.IntToRatExpr;
import hu.bme.mit.theta.core.type.inttype.IntType;
import hu.bme.mit.theta.core.type.rattype.RatAddExpr;
import hu.bme.mit.theta.core.type.rattype.RatDivExpr;
import hu.bme.mit.theta.core.type.rattype.RatEqExpr;
import hu.bme.mit.theta.core.type.rattype.RatGeqExpr;
import hu.bme.mit.theta.core.type.rattype.RatGtExpr;
import hu.bme.mit.theta.core.type.rattype.RatLeqExpr;
import hu.bme.mit.theta.core.type.rattype.RatLitExpr;
import hu.bme.mit.theta.core.type.rattype.RatLtExpr;
import hu.bme.mit.theta.core.type.rattype.RatMulExpr;
import hu.bme.mit.theta.core.type.rattype.RatNegExpr;
import hu.bme.mit.theta.core.type.rattype.RatNeqExpr;
import hu.bme.mit.theta.core.type.rattype.RatPosExpr;
import hu.bme.mit.theta.core.type.rattype.RatSubExpr;
import hu.bme.mit.theta.core.type.rattype.RatToIntExpr;
import hu.bme.mit.theta.core.type.rattype.RatType;
import org.kframework.mpfr.BigFloat;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;
import java.util.Optional;

import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.False;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Not;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.True;
import static hu.bme.mit.theta.core.type.bvtype.BvExprs.Bv;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;
import static hu.bme.mit.theta.core.type.rattype.RatExprs.Rat;
import static hu.bme.mit.theta.core.utils.SimplifierLevel.*;

public final class ExprSimplifier {

    private final SimplifierLevel level;

    private ExprSimplifier(final SimplifierLevel level) {
        this.level = level;
    }

    public static ExprSimplifier create() {
        return create(SimplifierLevel.FULL);
    }

    public static ExprSimplifier create(final SimplifierLevel level) {
        return new ExprSimplifier(level);
    }

    private final DispatchTable2<Valuation, Expr<?>> TABLE = DispatchTable2.<Valuation, Expr<?>>builder()

            // Boolean

            .addCase(NotExpr.class, this::simplifyNot)

            .addCase(ImplyExpr.class, this::simplifyImply)

            .addCase(IffExpr.class, this::simplifyIff)

            .addCase(XorExpr.class, this::simplifyXor)

            .addCase(AndExpr.class, this::simplifyAnd)

            .addCase(OrExpr.class, this::simplifyOr)

            // Rational

            .addCase(RatAddExpr.class, this::simplifyRatAdd)

            .addCase(RatSubExpr.class, this::simplifyRatSub)

            .addCase(RatPosExpr.class, this::simplifyRatPos)

            .addCase(RatNegExpr.class, this::simplifyRatNeg)

            .addCase(RatMulExpr.class, this::simplifyRatMul)

            .addCase(RatDivExpr.class, this::simplifyRatDiv)

            .addCase(RatEqExpr.class, this::simplifyRatEq)

            .addCase(RatNeqExpr.class, this::simplifyRatNeq)

            .addCase(RatGeqExpr.class, this::simplifyRatGeq)

            .addCase(RatGtExpr.class, this::simplifyRatGt)

            .addCase(RatLeqExpr.class, this::simplifyRatLeq)

            .addCase(RatLtExpr.class, this::simplifyRatLt)

            .addCase(RatToIntExpr.class, this::simplifyRatToInt)

            // Integer

            .addCase(IntToRatExpr.class, this::simplifyIntToRat)

            .addCase(IntAddExpr.class, this::simplifyIntAdd)

            .addCase(IntSubExpr.class, this::simplifyIntSub)

            .addCase(IntPosExpr.class, this::simplifyIntPos)

            .addCase(IntNegExpr.class, this::simplifyIntNeg)

            .addCase(IntMulExpr.class, this::simplifyIntMul)

            .addCase(IntDivExpr.class, this::simplifyIntDiv)

            .addCase(IntModExpr.class, this::simplifyMod)

            .addCase(IntRemExpr.class, this::simplifyRem)

            .addCase(IntEqExpr.class, this::simplifyIntEq)

            .addCase(IntNeqExpr.class, this::simplifyIntNeq)

            .addCase(IntGeqExpr.class, this::simplifyIntGeq)

            .addCase(IntGtExpr.class, this::simplifyIntGt)

            .addCase(IntLeqExpr.class, this::simplifyIntLeq)

            .addCase(IntLtExpr.class, this::simplifyIntLt)

            // Array

            .addCase(ArrayReadExpr.class, this::simplifyArrayRead)

            .addCase(ArrayWriteExpr.class, this::simplifyArrayWrite)

            //.addCase(ArrayInitExpr.class, this::simplifyArrayInit)
            .addCase(ArrayInitExpr.class, (arrayInitExpr, valuation) -> this.simplifyArrayInit(arrayInitExpr, valuation))

            // Bitvectors

            .addCase(BvConcatExpr.class, this::simplifyBvConcat)

            .addCase(BvExtractExpr.class, this::simplifyBvExtract)

            .addCase(BvZExtExpr.class, this::simplifyBvZExt)

            .addCase(BvSExtExpr.class, this::simplifyBvSExt)

            .addCase(BvAddExpr.class, this::simplifyBvAdd)

            .addCase(BvSubExpr.class, this::simplifyBvSub)

            .addCase(BvPosExpr.class, this::simplifyBvPos)

            .addCase(BvNegExpr.class, this::simplifyBvNeg)

            .addCase(BvMulExpr.class, this::simplifyBvMul)

            .addCase(BvUDivExpr.class, this::simplifyBvUDiv)

            .addCase(BvSDivExpr.class, this::simplifyBvSDiv)

            .addCase(BvSModExpr.class, this::simplifyBvSMod)

            .addCase(BvURemExpr.class, this::simplifyBvURem)

            .addCase(BvSRemExpr.class, this::simplifyBvSRem)

            .addCase(BvAndExpr.class, this::simplifyBvAnd)

            .addCase(BvOrExpr.class, this::simplifyBvOr)

            .addCase(BvXorExpr.class, this::simplifyBvXor)

            .addCase(BvNotExpr.class, this::simplifyBvNot)

            .addCase(BvShiftLeftExpr.class, this::simplifyBvShiftLeft)

            .addCase(BvArithShiftRightExpr.class, this::simplifyBvArithShiftRight)

            .addCase(BvLogicShiftRightExpr.class, this::simplifyBvLogicShiftRight)

            .addCase(BvRotateLeftExpr.class, this::simplifyBvRotateLeft)

            .addCase(BvRotateRightExpr.class, this::simplifyBvRotateRight)

            .addCase(BvEqExpr.class, this::simplifyBvEq)

            .addCase(BvNeqExpr.class, this::simplifyBvNeq)

            .addCase(BvUGeqExpr.class, this::simplifyBvUGeq)

            .addCase(BvUGtExpr.class, this::simplifyBvUGt)

            .addCase(BvULeqExpr.class, this::simplifyBvULeq)

            .addCase(BvULtExpr.class, this::simplifyBvULt)

            .addCase(BvSGeqExpr.class, this::simplifyBvSGeq)

            .addCase(BvSGtExpr.class, this::simplifyBvSGt)

            .addCase(BvSLeqExpr.class, this::simplifyBvSLeq)

            .addCase(BvSLtExpr.class, this::simplifyBvSLt)

            // Floating points

            .addCase(FpAddExpr.class, this::simplifyFpAdd)

            .addCase(FpSubExpr.class, this::simplifyFpSub)

            .addCase(FpPosExpr.class, this::simplifyFpPos)

            .addCase(FpNegExpr.class, this::simplifyFpNeg)

            .addCase(FpMulExpr.class, this::simplifyFpMul)

            .addCase(FpDivExpr.class, this::simplifyFpDiv)

            .addCase(FpEqExpr.class, this::simplifyFpEq)

            .addCase(FpAssignExpr.class, this::simplifyFpAssign)

            .addCase(FpGeqExpr.class, this::simplifyFpGeq)

            .addCase(FpLeqExpr.class, this::simplifyFpLeq)

            .addCase(FpGtExpr.class, this::simplifyFpGt)

            .addCase(FpLtExpr.class, this::simplifyFpLt)

            .addCase(FpNeqExpr.class, this::simplifyFpNeq)

            .addCase(FpAbsExpr.class, this::simplifyFpAbs)

            .addCase(FpRoundToIntegralExpr.class, this::simplifyFpRoundToIntegral)

            .addCase(FpMaxExpr.class, this::simplifyFpMax)

            .addCase(FpMinExpr.class, this::simplifyFpMin)

            .addCase(FpSqrtExpr.class, this::simplifyFpSqrt)

            .addCase(FpIsNanExpr.class, this::simplifyFpIsNan)

            .addCase(FpFromBvExpr.class, this::simplifyFpFromBv)

            .addCase(FpToBvExpr.class, this::simplifyFpToBv)

            .addCase(FpToFpExpr.class, this::simplifyFpToFp)

            // General

            .addCase(RefExpr.class, this::simplifyRef)

            .addCase(IteExpr.class, this::simplifyIte)

            // Default

            .addDefault((o, val) -> {
                final Expr<?> expr = (Expr<?>) o;
                return expr.map(e -> simplify(e, val));
            })

            .build();

    @SuppressWarnings("unchecked")
    public <T extends Type> Expr<T> simplify(final Expr<T> expr, final Valuation valuation) {
        return (Expr<T>) TABLE.dispatch(expr, valuation);
    }

    /*
     * General
     */

    private Expr<?> simplifyRef(final RefExpr<?> expr, final Valuation val) {
        return simplifyGenericRef(expr, val);
    }

    // TODO Eliminate helper method once the Java compiler is able to handle
    // this kind of type inference
    private <DeclType extends Type> Expr<DeclType> simplifyGenericRef(final RefExpr<DeclType> expr,
                                                                      final Valuation val) {
        final Optional<LitExpr<DeclType>> eval = val.eval(expr.getDecl());
        if (eval.isPresent()) {
            return eval.get();
        }

        return expr;
    }

    private Expr<?> simplifyIte(final IteExpr<?> expr, final Valuation val) {
        return simplifyGenericIte(expr, val);
    }

    // TODO Eliminate helper method once the Java compiler is able to handle
    // this kind of type inference
    private <ExprType extends Type> Expr<ExprType> simplifyGenericIte(final IteExpr<ExprType> expr,
                                                                      final Valuation val) {
        final Expr<BoolType> cond = simplify(expr.getCond(), val);

        if (cond instanceof TrueExpr) {
            final Expr<ExprType> then = simplify(expr.getThen(), val);
            return then;

        } else if (cond instanceof FalseExpr) {
            final Expr<ExprType> elze = simplify(expr.getElse(), val);
            return elze;
        }

        final Expr<ExprType> then = simplify(expr.getThen(), val);
        final Expr<ExprType> elze = simplify(expr.getElse(), val);

        return expr.with(cond, then, elze);
    }

    private Expr<?> simplifyArrayRead(final ArrayReadExpr<?, ?> expr, final Valuation val) {
        return simplifyGenericArrayRead(expr, val);
    }

    private <IT extends Type, ET extends Type> Expr<ET>
    simplifyGenericArrayRead(final ArrayReadExpr<IT, ET> expr, final Valuation val) {
        Expr<ArrayType<IT, ET>> arr = simplify(expr.getArray(), val);
        Expr<IT> index = simplify(expr.getIndex(), val);
        if (arr instanceof LitExpr<?> && index instanceof LitExpr<?>) { //The index is required to be a literal so that we can use 'equals' to compare it against existing keys in the array
            return expr.eval(val);
        }
        return expr.with(arr, index);
    }

    private Expr<?> simplifyArrayWrite(final ArrayWriteExpr<?, ?> expr, final Valuation val) {
        return simplifyGenericArrayWrite(expr, val);
    }

    private <IT extends Type, ET extends Type> Expr<ArrayType<IT, ET>>
    simplifyGenericArrayWrite(final ArrayWriteExpr<IT, ET> expr, final Valuation val) {
        Expr<ArrayType<IT, ET>> arr = simplify(expr.getArray(), val);
        Expr<IT> index = simplify(expr.getIndex(), val);
        Expr<ET> elem = simplify(expr.getElem(), val);
        if (arr instanceof LitExpr<?> && index instanceof LitExpr<?> && elem instanceof LitExpr<?>) {
            return expr.eval(val);
        }
        return expr.with(arr, index, elem);
    }

    private <IT extends Type, ET extends Type> Expr<ArrayType<IT, ET>>
    simplifyArrayInit(final ArrayInitExpr<IT, ET> t, final Valuation val) {
        boolean nonLiteralFound = false;
        List<Tuple2<Expr<IT>, Expr<ET>>> newElements = new ArrayList<>();
        Expr<ET> newElseElem = simplify(t.getElseElem(), val);
        if (!(newElseElem instanceof LitExpr)) nonLiteralFound = true;
        for (Tuple2<Expr<IT>, Expr<ET>> element : t.getElements()) {
            Expr<IT> newIndex = simplify(element.get1(), val);
            Expr<ET> newElement = simplify(element.get2(), val);
            newElements.add(Tuple2.of(newIndex, newElement));
            if (!(newElement instanceof LitExpr) || !(newIndex instanceof LitExpr))
                nonLiteralFound = true;
        }
        if (nonLiteralFound) return ArrayInitExpr.of(newElements, newElseElem, t.getType());
        else return t.eval(val);
    }

    /*
     * Booleans
     */

    private Expr<BoolType> simplifyNot(final NotExpr expr, final Valuation val) {
        final Expr<BoolType> op = simplify(expr.getOp(), val);
        if (op instanceof NotExpr) {
            return ((NotExpr) op).getOp();
        } else if (op instanceof TrueExpr) {
            return False();
        } else if (op instanceof FalseExpr) {
            return True();
        }

        return expr.with(op);
    }

    private Expr<BoolType> simplifyImply(final ImplyExpr expr, final Valuation val) {
        final Expr<BoolType> leftOp = simplify(expr.getLeftOp(), val);
        final Expr<BoolType> rightOp = simplify(expr.getRightOp(), val);

        if (leftOp instanceof BoolLitExpr && rightOp instanceof BoolLitExpr) {
            final boolean leftValue = ((BoolLitExpr) leftOp).getValue();
            final boolean rightValue = ((BoolLitExpr) rightOp).getValue();
            return Bool(!leftValue || rightValue);
        } else if (leftOp instanceof RefExpr && rightOp instanceof RefExpr) {
            if (level != LITERAL_ONLY && leftOp.equals(rightOp)) {
                return True();
            }
        }

        if (leftOp instanceof FalseExpr || rightOp instanceof TrueExpr) {
            return True();
        } else if (leftOp instanceof TrueExpr) {
            return rightOp;
        } else if (rightOp instanceof FalseExpr) {
            return simplify(Not(leftOp), val);
        }

        return expr.with(leftOp, rightOp);
    }

    private Expr<BoolType> simplifyIff(final IffExpr expr, final Valuation val) {
        final Expr<BoolType> leftOp = simplify(expr.getLeftOp(), val);
        final Expr<BoolType> rightOp = simplify(expr.getRightOp(), val);

        if (leftOp instanceof BoolLitExpr && rightOp instanceof BoolLitExpr) {
            final boolean leftValue = ((BoolLitExpr) leftOp).getValue();
            final boolean rightValue = ((BoolLitExpr) rightOp).getValue();
            return Bool(leftValue == rightValue);
        } else if (leftOp instanceof RefExpr && rightOp instanceof RefExpr) {
            if (level != LITERAL_ONLY && leftOp.equals(rightOp)) {
                return True();
            }
        }

        if (leftOp instanceof TrueExpr) {
            return rightOp;
        } else if (rightOp instanceof TrueExpr) {
            return leftOp;
        } else if (leftOp instanceof FalseExpr) {
            return simplify(Not(rightOp), val);
        } else if (rightOp instanceof FalseExpr) {
            return simplify(Not(leftOp), val);
        }

        return expr.with(leftOp, rightOp);
    }

    private Expr<BoolType> simplifyXor(final XorExpr expr, final Valuation val) {
        final Expr<BoolType> leftOp = simplify(expr.getLeftOp(), val);
        final Expr<BoolType> rightOp = simplify(expr.getRightOp(), val);

        if (leftOp instanceof BoolLitExpr && rightOp instanceof BoolLitExpr) {
            final boolean leftValue = ((BoolLitExpr) leftOp).getValue();
            final boolean rightValue = ((BoolLitExpr) rightOp).getValue();
            return Bool(leftValue != rightValue);
        } else if (leftOp instanceof RefExpr && rightOp instanceof RefExpr) {
            if (level != LITERAL_ONLY && leftOp.equals(rightOp)) {
                return False();
            }
        }

        if (leftOp instanceof TrueExpr) {
            return simplify(Not(rightOp), val);
        } else if (rightOp instanceof TrueExpr) {
            return simplify(Not(leftOp), val);
        } else if (leftOp instanceof FalseExpr) {
            return rightOp;
        } else if (rightOp instanceof FalseExpr) {
            return leftOp;
        }

        return expr.with(leftOp, rightOp);
    }

    private Expr<BoolType> simplifyAnd(final AndExpr expr, final Valuation val) {
        final List<Expr<BoolType>> ops = new ArrayList<>();

        if (expr.getOps().isEmpty()) {
            return True();
        }

        for (final Expr<BoolType> op : expr.getOps()) {
            final Expr<BoolType> opVisited = simplify(op, val);
            if (opVisited instanceof TrueExpr) {
                continue;
            } else if (opVisited instanceof FalseExpr) {
                return False();
            } else if (opVisited instanceof AndExpr) {
                final AndExpr andOp = (AndExpr) opVisited;
                ops.addAll(andOp.getOps());
            } else {
                ops.add(opVisited);
            }
        }

        if (ops.isEmpty()) {
            return True();
        } else if (ops.size() == 1) {
            return Utils.singleElementOf(ops);
        }

        return expr.with(ops);
    }

    private Expr<BoolType> simplifyOr(final OrExpr expr, final Valuation val) {
        final List<Expr<BoolType>> ops = new ArrayList<>();

        if (expr.getOps().isEmpty()) {
            return True();
        }

        for (final Expr<BoolType> op : expr.getOps()) {
            final Expr<BoolType> opVisited = simplify(op, val);
            if (opVisited instanceof FalseExpr) {
                continue;
            } else if (opVisited instanceof TrueExpr) {
                return True();
            } else if (opVisited instanceof OrExpr) {
                final OrExpr orOp = (OrExpr) opVisited;
                ops.addAll(orOp.getOps());
            } else {
                ops.add(opVisited);
            }
        }

        if (ops.isEmpty()) {
            return False();
        } else if (ops.size() == 1) {
            return Utils.singleElementOf(ops);
        }

        return expr.with(ops);
    }

    /*
     * Rationals
     */

    private Expr<RatType> simplifyRatAdd(final RatAddExpr expr, final Valuation val) {
        final List<Expr<RatType>> ops = new ArrayList<>();

        for (final Expr<RatType> op : expr.getOps()) {
            final Expr<RatType> opVisited = simplify(op, val);
            if (opVisited instanceof RatAddExpr) {
                final RatAddExpr addOp = (RatAddExpr) opVisited;
                ops.addAll(addOp.getOps());
            } else {
                ops.add(opVisited);
            }
        }
        var num = BigInteger.ZERO;
        var denom = BigInteger.ONE;

        for (final Iterator<Expr<RatType>> iterator = ops.iterator(); iterator.hasNext(); ) {
            final Expr<RatType> op = iterator.next();
            if (op instanceof RatLitExpr) {
                final RatLitExpr litOp = (RatLitExpr) op;
                num = num.multiply(litOp.getDenom()).add(denom.multiply(litOp.getNum()));
                denom = denom.multiply(litOp.getDenom());
                iterator.remove();
            }
        }

        final Expr<RatType> sum = Rat(num, denom);

        if (!sum.equals(Rat(0, 1))) {
            ops.add(0, sum);
        }

        if (ops.isEmpty()) {
            return Rat(0, 1);
        } else if (ops.size() == 1) {
            return Utils.singleElementOf(ops);
        }

        return expr.with(ops);
    }

    private Expr<RatType> simplifyRatSub(final RatSubExpr expr, final Valuation val) {
        final Expr<RatType> leftOp = simplify(expr.getLeftOp(), val);
        final Expr<RatType> rightOp = simplify(expr.getRightOp(), val);

        if (leftOp instanceof RatLitExpr && rightOp instanceof RatLitExpr) {
            final RatLitExpr leftLit = (RatLitExpr) leftOp;
            final RatLitExpr rightLit = (RatLitExpr) rightOp;
            return leftLit.sub(rightLit);
        }

        if (leftOp instanceof RefExpr && rightOp instanceof RefExpr) {
            if (leftOp.equals(rightOp)) {
                return Rat(0, 1);
            }
        }

        return expr.with(leftOp, rightOp);
    }

    private Expr<RatType> simplifyRatPos(final RatPosExpr expr, final Valuation val) {
        return simplify(expr.getOp(), val);
    }

    private Expr<RatType> simplifyRatNeg(final RatNegExpr expr, final Valuation val) {
        final Expr<RatType> op = simplify(expr.getOp(), val);

        if (op instanceof RatLitExpr) {
            final RatLitExpr litOp = (RatLitExpr) op;
            return litOp.neg();
        } else if (op instanceof RatNegExpr) {
            final RatNegExpr negOp = (RatNegExpr) op;
            return negOp.getOp();
        }

        return expr.with(op);
    }

    private Expr<RatType> simplifyRatMul(final RatMulExpr expr, final Valuation val) {
        final List<Expr<RatType>> ops = new ArrayList<>();

        for (final Expr<RatType> op : expr.getOps()) {
            final Expr<RatType> opVisited = simplify(op, val);
            if (opVisited instanceof RatMulExpr) {
                final RatMulExpr mulOp = (RatMulExpr) opVisited;
                ops.addAll(mulOp.getOps());
            } else {
                ops.add(opVisited);
            }
        }
        var num = BigInteger.ONE;
        var denom = BigInteger.ONE;

        for (final Iterator<Expr<RatType>> iterator = ops.iterator(); iterator.hasNext(); ) {
            final Expr<RatType> op = iterator.next();
            if (op instanceof RatLitExpr) {
                final RatLitExpr litOp = (RatLitExpr) op;
                num = num.multiply(litOp.getNum());
                denom = denom.multiply(litOp.getDenom());
                iterator.remove();
                if (num.compareTo(BigInteger.ZERO) == 0) {
                    return Rat(0, 1);
                }
            }
        }

        final Expr<RatType> prod = Rat(num, denom);

        if (!prod.equals(Rat(1, 1))) {
            ops.add(0, prod);
        }

        if (ops.isEmpty()) {
            return Rat(1, 1);
        } else if (ops.size() == 1) {
            return Utils.singleElementOf(ops);
        }

        return expr.with(ops);
    }

    private Expr<RatType> simplifyRatDiv(final RatDivExpr expr, final Valuation val) {
        final Expr<RatType> leftOp = simplify(expr.getLeftOp(), val);
        final Expr<RatType> rightOp = simplify(expr.getRightOp(), val);

        if (leftOp instanceof RatLitExpr && rightOp instanceof RatLitExpr) {
            final RatLitExpr leftLit = (RatLitExpr) leftOp;
            final RatLitExpr rightLit = (RatLitExpr) rightOp;
            return leftLit.div(rightLit);
        }

        return expr.with(leftOp, rightOp);
    }

    private Expr<BoolType> simplifyRatEq(final RatEqExpr expr, final Valuation val) {
        final Expr<RatType> leftOp = simplify(expr.getLeftOp(), val);
        final Expr<RatType> rightOp = simplify(expr.getRightOp(), val);

        if (leftOp instanceof RatLitExpr && rightOp instanceof RatLitExpr) {
            return Bool(leftOp.equals(rightOp));
        } else if (leftOp instanceof RefExpr && rightOp instanceof RefExpr) {
            if (level != LITERAL_ONLY && leftOp.equals(rightOp)) {
                return True();
            }
        }

        return expr.with(leftOp, rightOp);
    }

    private Expr<BoolType> simplifyRatNeq(final RatNeqExpr expr, final Valuation val) {
        final Expr<RatType> leftOp = simplify(expr.getLeftOp(), val);
        final Expr<RatType> rightOp = simplify(expr.getRightOp(), val);

        if (leftOp instanceof RatLitExpr && rightOp instanceof RatLitExpr) {
            return Bool(!leftOp.equals(rightOp));
        } else if (leftOp instanceof RefExpr && rightOp instanceof RefExpr) {
            if (level != LITERAL_ONLY && leftOp.equals(rightOp)) {
                return False();
            }
        }

        return expr.with(leftOp, rightOp);
    }

    private Expr<BoolType> simplifyRatGeq(final RatGeqExpr expr, final Valuation val) {
        final Expr<RatType> leftOp = simplify(expr.getLeftOp(), val);
        final Expr<RatType> rightOp = simplify(expr.getRightOp(), val);

        if (leftOp instanceof RatLitExpr && rightOp instanceof RatLitExpr) {
            final RatLitExpr leftLit = (RatLitExpr) leftOp;
            final RatLitExpr rightLit = (RatLitExpr) rightOp;
            return Bool(leftLit.compareTo(rightLit) >= 0);
        }

        if (leftOp instanceof RefExpr && rightOp instanceof RefExpr) {
            if (level != LITERAL_ONLY && leftOp.equals(rightOp)) {
                return True();
            }
        }

        return expr.with(leftOp, rightOp);
    }

    private Expr<BoolType> simplifyRatGt(final RatGtExpr expr, final Valuation val) {
        final Expr<RatType> leftOp = simplify(expr.getLeftOp(), val);
        final Expr<RatType> rightOp = simplify(expr.getRightOp(), val);

        if (leftOp instanceof RatLitExpr && rightOp instanceof RatLitExpr) {
            final RatLitExpr leftLit = (RatLitExpr) leftOp;
            final RatLitExpr rightLit = (RatLitExpr) rightOp;
            return Bool(leftLit.compareTo(rightLit) > 0);
        }

        if (leftOp instanceof RefExpr && rightOp instanceof RefExpr) {
            if (level != LITERAL_ONLY && leftOp.equals(rightOp)) {
                return False();
            }
        }

        return expr.with(leftOp, rightOp);
    }

    private Expr<BoolType> simplifyRatLeq(final RatLeqExpr expr, final Valuation val) {
        final Expr<RatType> leftOp = simplify(expr.getLeftOp(), val);
        final Expr<RatType> rightOp = simplify(expr.getRightOp(), val);

        if (leftOp instanceof RatLitExpr && rightOp instanceof RatLitExpr) {
            final RatLitExpr leftLit = (RatLitExpr) leftOp;
            final RatLitExpr rightLit = (RatLitExpr) rightOp;
            return Bool(leftLit.compareTo(rightLit) <= 0);
        }

        if (leftOp instanceof RefExpr && rightOp instanceof RefExpr) {
            if (level != LITERAL_ONLY && leftOp.equals(rightOp)) {
                return True();
            }
        }

        return expr.with(leftOp, rightOp);
    }

    private Expr<BoolType> simplifyRatLt(final RatLtExpr expr, final Valuation val) {
        final Expr<RatType> leftOp = simplify(expr.getLeftOp(), val);
        final Expr<RatType> rightOp = simplify(expr.getRightOp(), val);

        if (leftOp instanceof RatLitExpr && rightOp instanceof RatLitExpr) {
            final RatLitExpr leftLit = (RatLitExpr) leftOp;
            final RatLitExpr rightLit = (RatLitExpr) rightOp;
            return Bool(leftLit.compareTo(rightLit) < 0);
        }

        if (leftOp instanceof RefExpr && rightOp instanceof RefExpr) {
            if (level != LITERAL_ONLY && leftOp.equals(rightOp)) {
                return False();
            }
        }

        return expr.with(leftOp, rightOp);
    }

    private Expr<IntType> simplifyRatToInt(final RatToIntExpr expr, final Valuation val) {
        final Expr<RatType> op = simplify(expr.getOp(), val);

        if (op instanceof RatLitExpr) {
            final RatLitExpr litOp = (RatLitExpr) op;
            return litOp.toInt();
        }

        return expr.with(op);
    }

    /*
     * Integers
     */

    private Expr<RatType> simplifyIntToRat(final IntToRatExpr expr, final Valuation val) {
        final Expr<IntType> op = simplify(expr.getOp(), val);

        if (op instanceof IntLitExpr) {
            final IntLitExpr litOp = (IntLitExpr) op;
            return litOp.toRat();
        }

        return expr.with(op);
    }

    private Expr<IntType> simplifyIntAdd(final IntAddExpr expr, final Valuation val) {
        final List<Expr<IntType>> ops = new ArrayList<>();

        for (final Expr<IntType> op : expr.getOps()) {
            final Expr<IntType> opVisited = simplify(op, val);
            if (opVisited instanceof IntAddExpr) {
                final IntAddExpr addOp = (IntAddExpr) opVisited;
                ops.addAll(addOp.getOps());
            } else {
                ops.add(opVisited);
            }
        }
        var value = BigInteger.ZERO;

        for (final Iterator<Expr<IntType>> iterator = ops.iterator(); iterator.hasNext(); ) {
            final Expr<IntType> op = iterator.next();
            if (op instanceof IntLitExpr) {
                final IntLitExpr litOp = (IntLitExpr) op;
                value = value.add(litOp.getValue());
                iterator.remove();
            }
        }

        if (value.compareTo(BigInteger.ZERO) != 0) {
            final Expr<IntType> sum = Int(value);
            ops.add(sum);
        }

        if (ops.isEmpty()) {
            return Int(BigInteger.ZERO);
        } else if (ops.size() == 1) {
            return Utils.singleElementOf(ops);
        }

        return expr.with(ops);
    }

    private Expr<IntType> simplifyIntSub(final IntSubExpr expr, final Valuation val) {
        final Expr<IntType> leftOp = simplify(expr.getLeftOp(), val);
        final Expr<IntType> rightOp = simplify(expr.getRightOp(), val);

        if (leftOp instanceof IntLitExpr && rightOp instanceof IntLitExpr) {
            final IntLitExpr leftLit = (IntLitExpr) leftOp;
            final IntLitExpr rightLit = (IntLitExpr) rightOp;
            return leftLit.sub(rightLit);
        }

        if (leftOp instanceof RefExpr && rightOp instanceof RefExpr) {
            if (leftOp.equals(rightOp)) {
                return Int(BigInteger.ZERO);
            }
        }

        return expr.with(leftOp, rightOp);
    }

    private Expr<IntType> simplifyIntPos(final IntPosExpr expr, final Valuation val) {
        return simplify(expr.getOp(), val);
    }

    private Expr<IntType> simplifyIntNeg(final IntNegExpr expr, final Valuation val) {
        final Expr<IntType> op = simplify(expr.getOp(), val);

        if (op instanceof IntLitExpr) {
            final IntLitExpr litOp = (IntLitExpr) op;
            return litOp.neg();
        } else if (op instanceof IntNegExpr) {
            final IntNegExpr negOp = (IntNegExpr) op;
            return negOp.getOp();
        }

        return expr.with(op);
    }

    private Expr<IntType> simplifyIntMul(final IntMulExpr expr, final Valuation val) {
        final List<Expr<IntType>> ops = new ArrayList<>();

        for (final Expr<IntType> op : expr.getOps()) {
            final Expr<IntType> opVisited = simplify(op, val);
            if (opVisited instanceof IntMulExpr) {
                final IntMulExpr mulOp = (IntMulExpr) opVisited;
                ops.addAll(mulOp.getOps());
            } else {
                ops.add(opVisited);
            }
        }

        var value = BigInteger.ONE;
        for (final Iterator<Expr<IntType>> iterator = ops.iterator(); iterator.hasNext(); ) {
            final Expr<IntType> op = iterator.next();
            if (op instanceof IntLitExpr) {
                final IntLitExpr litOp = (IntLitExpr) op;
                value = value.multiply(litOp.getValue());
                iterator.remove();
                if (value.compareTo(BigInteger.ZERO) == 0) {
                    return Int(BigInteger.ZERO);
                }
            }
        }

        if (value.compareTo(BigInteger.ONE) != 0) {
            final Expr<IntType> prod = Int(value);
            ops.add(0, prod);
        }

        if (ops.isEmpty()) {
            return Int(BigInteger.ONE);
        } else if (ops.size() == 1) {
            return Utils.singleElementOf(ops);
        }

        return expr.with(ops);
    }

    private Expr<IntType> simplifyIntDiv(final IntDivExpr expr, final Valuation val) {
        final Expr<IntType> leftOp = simplify(expr.getLeftOp(), val);
        final Expr<IntType> rightOp = simplify(expr.getRightOp(), val);

        if (leftOp instanceof IntLitExpr && rightOp instanceof IntLitExpr) {
            final IntLitExpr leftLit = (IntLitExpr) leftOp;
            final IntLitExpr rightLit = (IntLitExpr) rightOp;
            return leftLit.div(rightLit);
        }

        return expr.with(leftOp, rightOp);
    }

    private Expr<IntType> simplifyMod(final IntModExpr expr, final Valuation val) {
        final Expr<IntType> leftOp = simplify(expr.getLeftOp(), val);
        final Expr<IntType> rightOp = simplify(expr.getRightOp(), val);

        if (leftOp instanceof IntLitExpr && rightOp instanceof IntLitExpr) {
            final IntLitExpr leftLit = (IntLitExpr) leftOp;
            final IntLitExpr rightLit = (IntLitExpr) rightOp;
            return leftLit.mod(rightLit);
        } else if (leftOp instanceof IntModExpr && ((IntModExpr) leftOp).getRightOp().equals(rightOp)) {
            return leftOp;
        }

        return expr.with(leftOp, rightOp);
    }

    private Expr<IntType> simplifyRem(final IntRemExpr expr, final Valuation val) {
        final Expr<IntType> leftOp = simplify(expr.getLeftOp(), val);
        final Expr<IntType> rightOp = simplify(expr.getRightOp(), val);

        if (leftOp instanceof IntLitExpr && rightOp instanceof IntLitExpr) {
            final IntLitExpr leftLit = (IntLitExpr) leftOp;
            final IntLitExpr rightLit = (IntLitExpr) rightOp;
            return leftLit.rem(rightLit);
        } else if (leftOp instanceof IntRemExpr && ((IntRemExpr) leftOp).getRightOp().equals(rightOp)) {
            return simplify(leftOp, val);
        }

        return expr.with(leftOp, rightOp);
    }

    private Expr<BoolType> simplifyIntEq(final IntEqExpr expr, final Valuation val) {
        final Expr<IntType> leftOp = simplify(expr.getLeftOp(), val);
        final Expr<IntType> rightOp = simplify(expr.getRightOp(), val);

        if (leftOp instanceof IntLitExpr && rightOp instanceof IntLitExpr) {
            return Bool(leftOp.equals(rightOp));
        } else if (leftOp instanceof RefExpr && rightOp instanceof RefExpr) {
            if (level != LITERAL_ONLY && leftOp.equals(rightOp)) {
                return True();
            }
        }

        return expr.with(leftOp, rightOp);
    }

    private Expr<BoolType> simplifyIntNeq(final IntNeqExpr expr, final Valuation val) {
        final Expr<IntType> leftOp = simplify(expr.getLeftOp(), val);
        final Expr<IntType> rightOp = simplify(expr.getRightOp(), val);

        if (leftOp instanceof IntLitExpr && rightOp instanceof IntLitExpr) {
            return Bool(!leftOp.equals(rightOp));
        } else if (leftOp instanceof RefExpr && rightOp instanceof RefExpr) {
            if (level != LITERAL_ONLY && leftOp.equals(rightOp)) {
                return False();
            }
        }

        return expr.with(leftOp, rightOp);
    }

    private Expr<BoolType> simplifyIntGeq(final IntGeqExpr expr, final Valuation val) {
        final Expr<IntType> leftOp = simplify(expr.getLeftOp(), val);
        final Expr<IntType> rightOp = simplify(expr.getRightOp(), val);

        if (leftOp instanceof IntLitExpr && rightOp instanceof IntLitExpr) {
            final IntLitExpr leftLit = (IntLitExpr) leftOp;
            final IntLitExpr rightLit = (IntLitExpr) rightOp;
            return Bool(leftLit.compareTo(rightLit) >= 0);
        }

        if (leftOp instanceof RefExpr && rightOp instanceof RefExpr) {
            if (level != LITERAL_ONLY && leftOp.equals(rightOp)) {
                return True();
            }
        }

        return expr.with(leftOp, rightOp);
    }

    private Expr<BoolType> simplifyIntGt(final IntGtExpr expr, final Valuation val) {
        final Expr<IntType> leftOp = simplify(expr.getLeftOp(), val);
        final Expr<IntType> rightOp = simplify(expr.getRightOp(), val);

        if (leftOp instanceof IntLitExpr && rightOp instanceof IntLitExpr) {
            final IntLitExpr leftLit = (IntLitExpr) leftOp;
            final IntLitExpr rightLit = (IntLitExpr) rightOp;
            return Bool(leftLit.compareTo(rightLit) > 0);
        }

        if (leftOp instanceof RefExpr && rightOp instanceof RefExpr) {
            if (level != LITERAL_ONLY && leftOp.equals(rightOp)) {
                return False();
            }
        }

        return expr.with(leftOp, rightOp);
    }

    private Expr<BoolType> simplifyIntLeq(final IntLeqExpr expr, final Valuation val) {
        final Expr<IntType> leftOp = simplify(expr.getLeftOp(), val);
        final Expr<IntType> rightOp = simplify(expr.getRightOp(), val);

        if (leftOp instanceof IntLitExpr && rightOp instanceof IntLitExpr) {
            final IntLitExpr leftLit = (IntLitExpr) leftOp;
            final IntLitExpr rightLit = (IntLitExpr) rightOp;
            return Bool(leftLit.compareTo(rightLit) <= 0);
        }

        if (leftOp instanceof RefExpr && rightOp instanceof RefExpr) {
            if (level != LITERAL_ONLY && leftOp.equals(rightOp)) {
                return True();
            }
        }

        return expr.with(leftOp, rightOp);
    }

    private Expr<BoolType> simplifyIntLt(final IntLtExpr expr, final Valuation val) {
        final Expr<IntType> leftOp = simplify(expr.getLeftOp(), val);
        final Expr<IntType> rightOp = simplify(expr.getRightOp(), val);

        if (leftOp instanceof IntLitExpr && rightOp instanceof IntLitExpr) {
            final IntLitExpr leftLit = (IntLitExpr) leftOp;
            final IntLitExpr rightLit = (IntLitExpr) rightOp;
            return Bool(leftLit.compareTo(rightLit) < 0);
        }

        if (leftOp instanceof RefExpr && rightOp instanceof RefExpr) {
            if (level != LITERAL_ONLY && leftOp.equals(rightOp)) {
                return False();
            }
        }

        return expr.with(leftOp, rightOp);
    }

    /*
     * Bitvectors
     */

    private Expr<BvType> simplifyBvConcat(final BvConcatExpr expr, final Valuation val) {
        final List<Expr<BvType>> ops = new ArrayList<>();

        for (final Expr<BvType> op : expr.getOps()) {
            final Expr<BvType> opVisited = simplify(op, val);
            if (opVisited instanceof BvConcatExpr) {
                final BvConcatExpr addOp = (BvConcatExpr) opVisited;
                ops.addAll(addOp.getOps());
            } else {
                ops.add(opVisited);
            }
        }
        BvLitExpr value = null;

        for (final Iterator<Expr<BvType>> iterator = ops.iterator(); iterator.hasNext(); ) {
            final Expr<BvType> op = iterator.next();
            if (op instanceof BvLitExpr) {
                final BvLitExpr litOp = (BvLitExpr) op;
                if (value == null) {
                    value = litOp;
                } else {
                    value = value.concat(litOp);
                }
//                iterator.remove();
            } else {
                return expr.withOps(ops);
            }
        }

        return value;
    }

    private Expr<BvType> simplifyBvExtract(final BvExtractExpr expr, final Valuation val) {
        final Expr<BvType> bitvec = simplify(expr.getBitvec(), val);

        if (bitvec instanceof BvLitExpr) {
            return ((BvLitExpr) bitvec).extract(expr.getFrom(), expr.getUntil());
        } else {
            return expr;
        }
    }

    private Expr<BvType> simplifyBvZExt(final BvZExtExpr expr, final Valuation val) {
        final Expr<BvType> bitvec = simplify(expr.getOp(), val);

        if (bitvec instanceof BvLitExpr) {
            return ((BvLitExpr) bitvec).zext(expr.getExtendType());
        } else {
            return expr;
        }
    }

    private Expr<BvType> simplifyBvSExt(final BvSExtExpr expr, final Valuation val) {
        final Expr<BvType> bitvec = simplify(expr.getOp(), val);

        if (bitvec instanceof BvLitExpr) {
            return ((BvLitExpr) bitvec).sext(expr.getExtendType());
        } else {
            return expr;
        }
    }

    private Expr<BvType> simplifyBvAdd(final BvAddExpr expr, final Valuation val) {
        final List<Expr<BvType>> ops = new ArrayList<>();

        for (final Expr<BvType> op : expr.getOps()) {
            final Expr<BvType> opVisited = simplify(op, val);
            if (opVisited instanceof BvAddExpr) {
                final BvAddExpr addOp = (BvAddExpr) opVisited;
                ops.addAll(addOp.getOps());
            } else {
                ops.add(opVisited);
            }
        }
        BvLitExpr value = Bv(new boolean[expr.getType().getSize()]);

        for (final Iterator<Expr<BvType>> iterator = ops.iterator(); iterator.hasNext(); ) {
            final Expr<BvType> op = iterator.next();
            if (op instanceof BvLitExpr) {
                final BvLitExpr litOp = (BvLitExpr) op;
                value = value.add(litOp);
                iterator.remove();
            }
        }

        if (!value.eq(Bv(new boolean[expr.getType().getSize()])).getValue()) {
            ops.add(value);
        }

        if (ops.isEmpty()) {
            return Bv(new boolean[expr.getType().getSize()]);
        } else if (ops.size() == 1) {
            return Utils.singleElementOf(ops);
        }

        return expr.with(ops);
    }

    private Expr<BvType> simplifyBvSub(final BvSubExpr expr, final Valuation val) {
        final Expr<BvType> leftOp = simplify(expr.getLeftOp(), val);
        final Expr<BvType> rightOp = simplify(expr.getRightOp(), val);

        if (leftOp instanceof BvLitExpr && rightOp instanceof BvLitExpr) {
            final BvLitExpr leftLit = (BvLitExpr) leftOp;
            final BvLitExpr rightLit = (BvLitExpr) rightOp;
            return leftLit.sub(rightLit);
        }

        if (leftOp instanceof RefExpr && rightOp instanceof RefExpr) {
            if (leftOp.equals(rightOp)) {
                return Bv(new boolean[expr.getType().getSize()]);
            }
        }

        return expr.with(leftOp, rightOp);
    }

    private Expr<BvType> simplifyBvPos(final BvPosExpr expr, final Valuation val) {
        return simplify(expr.getOp(), val);
    }

    private Expr<BvType> simplifyBvNeg(final BvNegExpr expr, final Valuation val) {
        final Expr<BvType> op = simplify(expr.getOp(), val);

        if (op instanceof BvLitExpr) {
            final BvLitExpr litOp = (BvLitExpr) op;
            return litOp.neg();
        } else if (op instanceof BvNegExpr) {
            final BvNegExpr negOp = (BvNegExpr) op;
            return negOp.getOp();
        }

        return expr.with(op);
    }

    private Expr<BvType> simplifyBvMul(final BvMulExpr expr, final Valuation val) {
        final List<Expr<BvType>> ops = new ArrayList<>();

        for (final Expr<BvType> op : expr.getOps()) {
            final Expr<BvType> opVisited = simplify(op, val);
            if (opVisited instanceof BvMulExpr) {
                final BvMulExpr mulOp = (BvMulExpr) opVisited;
                ops.addAll(mulOp.getOps());
            } else {
                ops.add(opVisited);
            }
        }

        final BvLitExpr ZERO = Bv(new boolean[expr.getType().getSize()]);
        final BvLitExpr ONE = Bv(new boolean[expr.getType().getSize()]);
        ONE.getValue()[expr.getType().getSize() - 1] = true; // 1

        BvLitExpr value = ONE;
        for (final Iterator<Expr<BvType>> iterator = ops.iterator(); iterator.hasNext(); ) {
            final Expr<BvType> op = iterator.next();
            if (op instanceof BvLitExpr) {
                final BvLitExpr litOp = (BvLitExpr) op;
                value = value.mul(litOp);
                iterator.remove();
                if (value.equals(ZERO)) {
                    return ZERO;
                }
            }
        }

        if (!value.equals(ONE)) {
            ops.add(0, value);
        }

        if (ops.isEmpty()) {
            return ONE;
        } else if (ops.size() == 1) {
            return Utils.singleElementOf(ops);
        }

        return expr.with(ops);
    }

    private Expr<BvType> simplifyBvUDiv(final BvUDivExpr expr, final Valuation val) {
        final Expr<BvType> leftOp = simplify(expr.getLeftOp(), val);
        final Expr<BvType> rightOp = simplify(expr.getRightOp(), val);

        if (leftOp instanceof BvLitExpr && rightOp instanceof BvLitExpr) {
            final BvLitExpr leftLit = (BvLitExpr) leftOp;
            final BvLitExpr rightLit = (BvLitExpr) rightOp;
            return leftLit.udiv(rightLit);
        }

        if (leftOp instanceof RefExpr && rightOp instanceof RefExpr) {
            if (leftOp.equals(rightOp)) {
                final BvLitExpr ONE = Bv(new boolean[expr.getType().getSize()]);
                ONE.getValue()[expr.getType().getSize() - 1] = true; // 1
                return ONE;
            }
        }

        return expr.with(leftOp, rightOp);
    }

    private Expr<BvType> simplifyBvSDiv(final BvSDivExpr expr, final Valuation val) {
        final Expr<BvType> leftOp = simplify(expr.getLeftOp(), val);
        final Expr<BvType> rightOp = simplify(expr.getRightOp(), val);

        if (leftOp instanceof BvLitExpr && rightOp instanceof BvLitExpr) {
            final BvLitExpr leftLit = (BvLitExpr) leftOp;
            final BvLitExpr rightLit = (BvLitExpr) rightOp;
            return leftLit.sdiv(rightLit);
        }

        if (leftOp instanceof RefExpr && rightOp instanceof RefExpr) {
            if (leftOp.equals(rightOp)) {
                final BvLitExpr ONE = Bv(new boolean[expr.getType().getSize()]);
                ONE.getValue()[expr.getType().getSize() - 1] = true; // 1
                return ONE;
            }
        }

        return expr.with(leftOp, rightOp);
    }

    private Expr<BvType> simplifyBvSMod(final BvSModExpr expr, final Valuation val) {
        final Expr<BvType> leftOp = simplify(expr.getLeftOp(), val);
        final Expr<BvType> rightOp = simplify(expr.getRightOp(), val);

        if (leftOp instanceof BvLitExpr && rightOp instanceof BvLitExpr) {
            final BvLitExpr leftLit = (BvLitExpr) leftOp;
            final BvLitExpr rightLit = (BvLitExpr) rightOp;
            return leftLit.smod(rightLit);
        }

        if (leftOp instanceof RefExpr && rightOp instanceof RefExpr) {
            if (leftOp.equals(rightOp)) {
                return Bv(new boolean[expr.getType().getSize()]);
            }
        }

        return expr.with(leftOp, rightOp);
    }

    private Expr<BvType> simplifyBvURem(final BvURemExpr expr, final Valuation val) {
        final Expr<BvType> leftOp = simplify(expr.getLeftOp(), val);
        final Expr<BvType> rightOp = simplify(expr.getRightOp(), val);

        if (leftOp instanceof BvLitExpr && rightOp instanceof BvLitExpr) {
            final BvLitExpr leftLit = (BvLitExpr) leftOp;
            final BvLitExpr rightLit = (BvLitExpr) rightOp;
            return leftLit.urem(rightLit);
        }

        if (leftOp instanceof RefExpr && rightOp instanceof RefExpr) {
            if (leftOp.equals(rightOp)) {
                return Bv(new boolean[expr.getType().getSize()]);
            }
        }

        return expr.with(leftOp, rightOp);
    }

    private Expr<BvType> simplifyBvSRem(final BvSRemExpr expr, final Valuation val) {
        final Expr<BvType> leftOp = simplify(expr.getLeftOp(), val);
        final Expr<BvType> rightOp = simplify(expr.getRightOp(), val);

        if (leftOp instanceof BvLitExpr && rightOp instanceof BvLitExpr) {
            final BvLitExpr leftLit = (BvLitExpr) leftOp;
            final BvLitExpr rightLit = (BvLitExpr) rightOp;
            return leftLit.srem(rightLit);
        }

        if (leftOp instanceof RefExpr && rightOp instanceof RefExpr) {
            if (leftOp.equals(rightOp)) {
                return Bv(new boolean[expr.getType().getSize()]);
            }
        }

        return expr.with(leftOp, rightOp);
    }

    private Expr<BvType> simplifyBvAnd(final BvAndExpr expr, final Valuation val) {
        final List<Expr<BvType>> ops = new ArrayList<>();

        for (final Expr<BvType> op : expr.getOps()) {
            final Expr<BvType> opVisited = simplify(op, val);
            if (opVisited instanceof BvAndExpr) {
                final BvAndExpr addOp = (BvAndExpr) opVisited;
                ops.addAll(addOp.getOps());
            } else {
                ops.add(opVisited);
            }
        }
        BvLitExpr ONES = Bv(new boolean[expr.getType().getSize()]);
        for (int i = 0; i < expr.getType().getSize(); i++) {
            ONES.getValue()[i] = true;
        }

        BvLitExpr value = ONES;

        for (final Iterator<Expr<BvType>> iterator = ops.iterator(); iterator.hasNext(); ) {
            final Expr<BvType> op = iterator.next();
            if (op instanceof BvLitExpr) {
                final BvLitExpr litOp = (BvLitExpr) op;
                value = value.and(litOp);
                iterator.remove();
            }
        }

        if (!value.equals(ONES)) {
            ops.add(value);
        }

        if (ops.isEmpty()) {
            return ONES;
        } else if (ops.size() == 1) {
            return Utils.singleElementOf(ops);
        }

        return expr.with(ops);
    }

    private Expr<BvType> simplifyBvOr(final BvOrExpr expr, final Valuation val) {
        final List<Expr<BvType>> ops = new ArrayList<>();

        for (final Expr<BvType> op : expr.getOps()) {
            final Expr<BvType> opVisited = simplify(op, val);
            if (opVisited instanceof BvOrExpr) {
                final BvOrExpr addOp = (BvOrExpr) opVisited;
                ops.addAll(addOp.getOps());
            } else {
                ops.add(opVisited);
            }
        }
        BvLitExpr ZEROS = Bv(new boolean[expr.getType().getSize()]);

        BvLitExpr value = ZEROS;

        for (final Iterator<Expr<BvType>> iterator = ops.iterator(); iterator.hasNext(); ) {
            final Expr<BvType> op = iterator.next();
            if (op instanceof BvLitExpr) {
                final BvLitExpr litOp = (BvLitExpr) op;
                value = value.or(litOp);
                iterator.remove();
            }
        }

        if (!value.equals(ZEROS)) {
            ops.add(value);
        }

        if (ops.isEmpty()) {
            return ZEROS;
        } else if (ops.size() == 1) {
            return Utils.singleElementOf(ops);
        }

        return expr.with(ops);
    }

    private Expr<BvType> simplifyBvXor(final BvXorExpr expr, final Valuation val) {
        final List<Expr<BvType>> ops = new ArrayList<>();

        for (final Expr<BvType> op : expr.getOps()) {
            final Expr<BvType> opVisited = simplify(op, val);
            if (opVisited instanceof BvXorExpr) {
                final BvXorExpr addOp = (BvXorExpr) opVisited;
                ops.addAll(addOp.getOps());
            } else {
                ops.add(opVisited);
            }
        }
        BvLitExpr ZEROS = Bv(new boolean[expr.getType().getSize()]);

        BvLitExpr value = ZEROS;

        for (final Iterator<Expr<BvType>> iterator = ops.iterator(); iterator.hasNext(); ) {
            final Expr<BvType> op = iterator.next();
            if (op instanceof BvLitExpr) {
                final BvLitExpr litOp = (BvLitExpr) op;
                value = value.xor(litOp);
                iterator.remove();
            }
        }

        if (!value.equals(ZEROS)) {
            ops.add(value);
        }

        if (ops.isEmpty()) {
            return ZEROS;
        } else if (ops.size() == 1) {
            return Utils.singleElementOf(ops);
        }

        return expr.with(ops);
    }

    private Expr<BvType> simplifyBvNot(final BvNotExpr expr, final Valuation val) {
        final Expr<BvType> op = simplify(expr.getOp(), val);

        if (op instanceof BvLitExpr) {
            final BvLitExpr litOp = (BvLitExpr) op;
            return litOp.not();
        } else if (op instanceof BvNotExpr) {
            final BvNotExpr notOp = (BvNotExpr) op;
            return notOp.getOp();
        }

        return expr.with(op);
    }

    private Expr<BvType> simplifyBvShiftLeft(final BvShiftLeftExpr expr, final Valuation val) {
        final Expr<BvType> leftOp = simplify(expr.getLeftOp(), val);
        final Expr<BvType> rightOp = simplify(expr.getRightOp(), val);

        if (leftOp instanceof BvLitExpr && rightOp instanceof BvLitExpr) {
            final BvLitExpr leftLit = (BvLitExpr) leftOp;
            final BvLitExpr rightLit = (BvLitExpr) rightOp;
            return leftLit.shiftLeft(rightLit);
        }

        return expr.with(leftOp, rightOp);
    }

    private Expr<BvType> simplifyBvArithShiftRight(final BvArithShiftRightExpr expr, final Valuation val) {
        final Expr<BvType> leftOp = simplify(expr.getLeftOp(), val);
        final Expr<BvType> rightOp = simplify(expr.getRightOp(), val);

        if (leftOp instanceof BvLitExpr && rightOp instanceof BvLitExpr) {
            final BvLitExpr leftLit = (BvLitExpr) leftOp;
            final BvLitExpr rightLit = (BvLitExpr) rightOp;
            return leftLit.arithShiftRight(rightLit);
        }

        return expr.with(leftOp, rightOp);
    }

    private Expr<BvType> simplifyBvLogicShiftRight(final BvLogicShiftRightExpr expr, final Valuation val) {
        final Expr<BvType> leftOp = simplify(expr.getLeftOp(), val);
        final Expr<BvType> rightOp = simplify(expr.getRightOp(), val);

        if (leftOp instanceof BvLitExpr && rightOp instanceof BvLitExpr) {
            final BvLitExpr leftLit = (BvLitExpr) leftOp;
            final BvLitExpr rightLit = (BvLitExpr) rightOp;
            return leftLit.logicShiftRight(rightLit);
        }

        return expr.with(leftOp, rightOp);
    }

    private Expr<BvType> simplifyBvRotateLeft(final BvRotateLeftExpr expr, final Valuation val) {
        final Expr<BvType> leftOp = simplify(expr.getLeftOp(), val);
        final Expr<BvType> rightOp = simplify(expr.getRightOp(), val);

        if (leftOp instanceof BvLitExpr && rightOp instanceof BvLitExpr) {
            final BvLitExpr leftLit = (BvLitExpr) leftOp;
            final BvLitExpr rightLit = (BvLitExpr) rightOp;
            return leftLit.rotateLeft(rightLit);
        }

        return expr.with(leftOp, rightOp);
    }

    private Expr<BvType> simplifyBvRotateRight(final BvRotateRightExpr expr, final Valuation val) {
        final Expr<BvType> leftOp = simplify(expr.getLeftOp(), val);
        final Expr<BvType> rightOp = simplify(expr.getRightOp(), val);

        if (leftOp instanceof BvLitExpr && rightOp instanceof BvLitExpr) {
            final BvLitExpr leftLit = (BvLitExpr) leftOp;
            final BvLitExpr rightLit = (BvLitExpr) rightOp;
            return leftLit.rotateRight(rightLit);
        }

        return expr.with(leftOp, rightOp);
    }

    private Expr<BoolType> simplifyBvEq(final BvEqExpr expr, final Valuation val) {
        final Expr<BvType> leftOp = simplify(expr.getLeftOp(), val);
        final Expr<BvType> rightOp = simplify(expr.getRightOp(), val);

        if (leftOp instanceof BvLitExpr && rightOp instanceof BvLitExpr) {
            return Bool(leftOp.equals(rightOp));
        } else if (leftOp instanceof RefExpr && rightOp instanceof RefExpr) {
            if (level != LITERAL_ONLY && leftOp.equals(rightOp)) {
                return True();
            }
        }

        return expr.with(leftOp, rightOp);
    }

    private Expr<BoolType> simplifyBvNeq(final BvNeqExpr expr, final Valuation val) {
        final Expr<BvType> leftOp = simplify(expr.getLeftOp(), val);
        final Expr<BvType> rightOp = simplify(expr.getRightOp(), val);

        if (leftOp instanceof BvLitExpr && rightOp instanceof BvLitExpr) {
            return Bool(!leftOp.equals(rightOp));
        } else if (leftOp instanceof RefExpr && rightOp instanceof RefExpr) {
            if (level != LITERAL_ONLY && leftOp.equals(rightOp)) {
                return False();
            }
        }

        return expr.with(leftOp, rightOp);
    }

    private Expr<BoolType> simplifyBvUGeq(final BvUGeqExpr expr, final Valuation val) {
        final Expr<BvType> leftOp = simplify(expr.getLeftOp(), val);
        final Expr<BvType> rightOp = simplify(expr.getRightOp(), val);

        if (leftOp instanceof BvLitExpr && rightOp instanceof BvLitExpr) {
            final BvLitExpr leftLit = (BvLitExpr) leftOp;
            final BvLitExpr rightLit = (BvLitExpr) rightOp;
            return leftLit.uge(rightLit);
        }

        if (leftOp instanceof RefExpr && rightOp instanceof RefExpr) {
            if (level != LITERAL_ONLY && leftOp.equals(rightOp)) {
                return True();
            }
        }

        return expr.with(leftOp, rightOp);
    }

    private Expr<BoolType> simplifyBvUGt(final BvUGtExpr expr, final Valuation val) {
        final Expr<BvType> leftOp = simplify(expr.getLeftOp(), val);
        final Expr<BvType> rightOp = simplify(expr.getRightOp(), val);

        if (leftOp instanceof BvLitExpr && rightOp instanceof BvLitExpr) {
            final BvLitExpr leftLit = (BvLitExpr) leftOp;
            final BvLitExpr rightLit = (BvLitExpr) rightOp;
            return leftLit.ugt(rightLit);
        }

        if (leftOp instanceof RefExpr && rightOp instanceof RefExpr) {
            if (level != LITERAL_ONLY && leftOp.equals(rightOp)) {
                return False();
            }
        }

        return expr.with(leftOp, rightOp);
    }

    private Expr<BoolType> simplifyBvULeq(final BvULeqExpr expr, final Valuation val) {
        final Expr<BvType> leftOp = simplify(expr.getLeftOp(), val);
        final Expr<BvType> rightOp = simplify(expr.getRightOp(), val);

        if (leftOp instanceof BvLitExpr && rightOp instanceof BvLitExpr) {
            final BvLitExpr leftLit = (BvLitExpr) leftOp;
            final BvLitExpr rightLit = (BvLitExpr) rightOp;
            return leftLit.ule(rightLit);
        }

        if (leftOp instanceof RefExpr && rightOp instanceof RefExpr) {
            if (level != LITERAL_ONLY && leftOp.equals(rightOp)) {
                return True();
            }
        }

        return expr.with(leftOp, rightOp);
    }

    private Expr<BoolType> simplifyBvULt(final BvULtExpr expr, final Valuation val) {
        final Expr<BvType> leftOp = simplify(expr.getLeftOp(), val);
        final Expr<BvType> rightOp = simplify(expr.getRightOp(), val);

        if (leftOp instanceof BvLitExpr && rightOp instanceof BvLitExpr) {
            final BvLitExpr leftLit = (BvLitExpr) leftOp;
            final BvLitExpr rightLit = (BvLitExpr) rightOp;
            return leftLit.ult(rightLit);
        }

        if (leftOp instanceof RefExpr && rightOp instanceof RefExpr) {
            if (level != LITERAL_ONLY && leftOp.equals(rightOp)) {
                return False();
            }
        }

        return expr.with(leftOp, rightOp);
    }

    private Expr<BoolType> simplifyBvSGeq(final BvSGeqExpr expr, final Valuation val) {
        final Expr<BvType> leftOp = simplify(expr.getLeftOp(), val);
        final Expr<BvType> rightOp = simplify(expr.getRightOp(), val);

        if (leftOp instanceof BvLitExpr && rightOp instanceof BvLitExpr) {
            final BvLitExpr leftLit = (BvLitExpr) leftOp;
            final BvLitExpr rightLit = (BvLitExpr) rightOp;
            return leftLit.sge(rightLit);
        }

        if (leftOp instanceof RefExpr && rightOp instanceof RefExpr) {
            if (level != LITERAL_ONLY && leftOp.equals(rightOp)) {
                return True();
            }
        }

        return expr.with(leftOp, rightOp);
    }

    private Expr<BoolType> simplifyBvSGt(final BvSGtExpr expr, final Valuation val) {
        final Expr<BvType> leftOp = simplify(expr.getLeftOp(), val);
        final Expr<BvType> rightOp = simplify(expr.getRightOp(), val);

        if (leftOp instanceof BvLitExpr && rightOp instanceof BvLitExpr) {
            final BvLitExpr leftLit = (BvLitExpr) leftOp;
            final BvLitExpr rightLit = (BvLitExpr) rightOp;
            return leftLit.sgt(rightLit);
        }

        if (leftOp instanceof RefExpr && rightOp instanceof RefExpr) {
            if (level != LITERAL_ONLY && leftOp.equals(rightOp)) {
                return False();
            }
        }

        return expr.with(leftOp, rightOp);
    }

    private Expr<BoolType> simplifyBvSLeq(final BvSLeqExpr expr, final Valuation val) {
        final Expr<BvType> leftOp = simplify(expr.getLeftOp(), val);
        final Expr<BvType> rightOp = simplify(expr.getRightOp(), val);

        if (leftOp instanceof BvLitExpr && rightOp instanceof BvLitExpr) {
            final BvLitExpr leftLit = (BvLitExpr) leftOp;
            final BvLitExpr rightLit = (BvLitExpr) rightOp;
            return leftLit.sle(rightLit);
        }

        if (leftOp instanceof RefExpr && rightOp instanceof RefExpr) {
            if (level != LITERAL_ONLY && leftOp.equals(rightOp)) {
                return True();
            }
        }

        return expr.with(leftOp, rightOp);
    }

    private Expr<BoolType> simplifyBvSLt(final BvSLtExpr expr, final Valuation val) {
        final Expr<BvType> leftOp = simplify(expr.getLeftOp(), val);
        final Expr<BvType> rightOp = simplify(expr.getRightOp(), val);

        if (leftOp instanceof BvLitExpr && rightOp instanceof BvLitExpr) {
            final BvLitExpr leftLit = (BvLitExpr) leftOp;
            final BvLitExpr rightLit = (BvLitExpr) rightOp;
            return leftLit.slt(rightLit);
        }

        if (leftOp instanceof RefExpr && rightOp instanceof RefExpr) {
            if (level != LITERAL_ONLY && leftOp.equals(rightOp)) {
                return False();
            }
        }

        return expr.with(leftOp, rightOp);
    }

    private Expr<FpType> simplifyFpAdd(final FpAddExpr expr, final Valuation val) {
        final List<Expr<FpType>> ops = new ArrayList<>();

        for (final Expr<FpType> op : expr.getOps()) {
            final Expr<FpType> opVisited = simplify(op, val);
            if (opVisited instanceof FpAddExpr) {
                final FpAddExpr addOp = (FpAddExpr) opVisited;
                ops.addAll(addOp.getOps());
            } else {
                ops.add(opVisited);
            }
        }
        final FpLitExpr zero = FpUtils.bigFloatToFpLitExpr(BigFloat.zero(expr.getType().getSignificand()), expr.getType());
        FpLitExpr value = zero;

        for (final Iterator<Expr<FpType>> iterator = ops.iterator(); iterator.hasNext(); ) {
            final Expr<FpType> op = iterator.next();
            if (op instanceof FpLitExpr) {
                final FpLitExpr litOp = (FpLitExpr) op;
                value = value.add(expr.getRoundingMode(), litOp);
                iterator.remove();
            }
        }

        if (!value.equals(zero)) {
            ops.add(value);
        }

        if (ops.isEmpty()) {
            return zero;
        } else if (ops.size() == 1) {
            return Utils.singleElementOf(ops);
        }

        return expr.with(ops);
    }

    private Expr<FpType> simplifyFpSub(final FpSubExpr expr, final Valuation val) {
        final Expr<FpType> leftOp = simplify(expr.getLeftOp(), val);
        final Expr<FpType> rightOp = simplify(expr.getRightOp(), val);

        if (leftOp instanceof FpLitExpr && rightOp instanceof FpLitExpr) {
            final FpLitExpr leftLit = (FpLitExpr) leftOp;
            final FpLitExpr rightLit = (FpLitExpr) rightOp;
            return leftLit.sub(expr.getRoundingMode(), rightLit);
        }

        if (leftOp instanceof RefExpr && rightOp instanceof RefExpr) {
            if (leftOp.equals(rightOp)) {
                return FpUtils.bigFloatToFpLitExpr(BigFloat.zero(expr.getType().getSignificand()), expr.getType());
            }
        }

        return expr.with(leftOp, rightOp);
    }

    private Expr<FpType> simplifyFpPos(final FpPosExpr expr, final Valuation val) {
        return simplify(expr.getOp(), val);
    }

    private Expr<FpType> simplifyFpNeg(final FpNegExpr expr, final Valuation val) {
        final Expr<FpType> op = simplify(expr.getOp(), val);

        if (op instanceof FpLitExpr) {
            final FpLitExpr litOp = (FpLitExpr) op;
            return litOp.neg();
        } else if (op instanceof FpNegExpr) {
            final FpNegExpr negOp = (FpNegExpr) op;
            return negOp.getOp();
        }

        return expr.with(op);
    }

    private Expr<FpType> simplifyFpAbs(final FpAbsExpr expr, final Valuation val) {
        final Expr<FpType> op = simplify(expr.getOp(), val);

        if (op instanceof FpAbsExpr) {
            final FpAbsExpr absOp = (FpAbsExpr) op;
            return absOp.getOp();
        }

        return expr.with(op);
    }

    private Expr<BoolType> simplifyFpIsNan(final FpIsNanExpr expr, final Valuation val) {
        final Expr<FpType> op = simplify(expr.getOp(), val);

        if (op instanceof FpLitExpr) {
            return Bool(((FpLitExpr) op).isNaN());
        }

        return expr.with(op);
    }

    private Expr<BoolType> simplifyFpIsInfinite(final FpIsInfiniteExpr expr, final Valuation val) {
        final Expr<FpType> op = simplify(expr.getOp(), val);

        if (op instanceof FpLitExpr) {
            return Bool((((FpLitExpr) op).isNegativeInfinity() || ((FpLitExpr) op).isPositiveInfinity()));
        }

        return expr.with(op);
    }

    private Expr<FpType> simplifyFpRoundToIntegral(final FpRoundToIntegralExpr expr, final Valuation val) {
        final Expr<FpType> op = simplify(expr.getOp(), val);

        if (op instanceof FpRoundToIntegralExpr) {
            final FpRoundToIntegralExpr rndOp = (FpRoundToIntegralExpr) op;
            return rndOp.getOp();
        }

        return expr.with(op);
    }

    private Expr<FpType> simplifyFpMul(final FpMulExpr expr, final Valuation val) {
        final List<Expr<FpType>> ops = new ArrayList<>();

        for (final Expr<FpType> op : expr.getOps()) {
            final Expr<FpType> opVisited = simplify(op, val);
            if (opVisited instanceof FpMulExpr) {
                final FpMulExpr mulOp = (FpMulExpr) opVisited;
                ops.addAll(mulOp.getOps());
            } else {
                ops.add(opVisited);
            }
        }

        final FpLitExpr ZERO = FpUtils.bigFloatToFpLitExpr(BigFloat.zero(expr.getType().getSignificand()), expr.getType());
        final FpLitExpr ONE = FpUtils.bigFloatToFpLitExpr(new BigFloat(1.0f, FpUtils.getMathContext(expr.getType(), expr.getRoundingMode())), expr.getType());

        FpLitExpr value = ONE;
        for (final Iterator<Expr<FpType>> iterator = ops.iterator(); iterator.hasNext(); ) {
            final Expr<FpType> op = iterator.next();
            if (op instanceof FpLitExpr) {
                final FpLitExpr litOp = (FpLitExpr) op;
                value = value.mul(expr.getRoundingMode(), litOp);
                iterator.remove();
                if (value.equals(ZERO)) {
                    return ZERO;
                }
            }
        }

        if (!value.equals(ONE)) {
            ops.add(0, value);
        }

        if (ops.isEmpty()) {
            return ONE;
        } else if (ops.size() == 1) {
            return Utils.singleElementOf(ops);
        }

        return expr.with(ops);
    }

    private Expr<FpType> simplifyFpDiv(final FpDivExpr expr, final Valuation val) {
        if (true) return expr; // Rationale: https://github.com/ftsrg/theta/issues/180
        final Expr<FpType> leftOp = simplify(expr.getLeftOp(), val);
        final Expr<FpType> rightOp = simplify(expr.getRightOp(), val);

        if (leftOp instanceof FpLitExpr && rightOp instanceof FpLitExpr) {
            final FpLitExpr leftLit = (FpLitExpr) leftOp;
            final FpLitExpr rightLit = (FpLitExpr) rightOp;
            return leftLit.div(expr.getRoundingMode(), rightLit);
        }

        if (leftOp instanceof RefExpr && rightOp instanceof RefExpr) {
            if (leftOp.equals(rightOp)) {
                return FpUtils.bigFloatToFpLitExpr(new BigFloat(1.0f, FpUtils.getMathContext(expr.getType(), expr.getRoundingMode())), expr.getType());
            }
        }

        return expr.with(leftOp, rightOp);
    }

    private Expr<BoolType> simplifyFpEq(final FpEqExpr expr, final Valuation val) {
        final Expr<FpType> leftOp = simplify(expr.getLeftOp(), val);
        final Expr<FpType> rightOp = simplify(expr.getRightOp(), val);

        if (leftOp instanceof FpLitExpr && rightOp instanceof FpLitExpr) {
            return Bool(leftOp.equals(rightOp));
        } else if (leftOp instanceof RefExpr && rightOp instanceof RefExpr) {
            if (level != LITERAL_ONLY && leftOp.equals(rightOp)) {
                return True();
            }
        }

        return expr.with(leftOp, rightOp);
    }

    private Expr<BoolType> simplifyFpAssign(final FpAssignExpr expr, final Valuation val) {
        final Expr<FpType> leftOp = simplify(expr.getLeftOp(), val);
        final Expr<FpType> rightOp = simplify(expr.getRightOp(), val);

        if (leftOp instanceof FpLitExpr && rightOp instanceof FpLitExpr) {
            return Bool(leftOp.equals(rightOp));
        }

        return expr.with(leftOp, rightOp);
    }

    private Expr<BoolType> simplifyFpGeq(final FpGeqExpr expr, final Valuation val) {
        final Expr<FpType> leftOp = simplify(expr.getLeftOp(), val);
        final Expr<FpType> rightOp = simplify(expr.getRightOp(), val);

        if (leftOp instanceof FpLitExpr && rightOp instanceof FpLitExpr) {
            return expr.eval(val);
        }

        return expr.with(leftOp, rightOp);
    }

    private Expr<BoolType> simplifyFpLeq(final FpLeqExpr expr, final Valuation val) {
        final Expr<FpType> leftOp = simplify(expr.getLeftOp(), val);
        final Expr<FpType> rightOp = simplify(expr.getRightOp(), val);

        if (leftOp instanceof FpLitExpr && rightOp instanceof FpLitExpr) {
            return expr.eval(val);
        }

        return expr.with(leftOp, rightOp);
    }

    private Expr<BoolType> simplifyFpGt(final FpGtExpr expr, final Valuation val) {
        final Expr<FpType> leftOp = simplify(expr.getLeftOp(), val);
        final Expr<FpType> rightOp = simplify(expr.getRightOp(), val);

        if (leftOp instanceof FpLitExpr && rightOp instanceof FpLitExpr) {
            return expr.eval(val);
        }

        return expr.with(leftOp, rightOp);
    }

    private Expr<BoolType> simplifyFpLt(final FpLtExpr expr, final Valuation val) {
        final Expr<FpType> leftOp = simplify(expr.getLeftOp(), val);
        final Expr<FpType> rightOp = simplify(expr.getRightOp(), val);

        if (leftOp instanceof FpLitExpr && rightOp instanceof FpLitExpr) {
            return expr.eval(val);
        }

        return expr.with(leftOp, rightOp);
    }


    private Expr<BoolType> simplifyFpNeq(final FpNeqExpr expr, final Valuation val) {
        final Expr<FpType> leftOp = simplify(expr.getLeftOp(), val);
        final Expr<FpType> rightOp = simplify(expr.getRightOp(), val);

        if (leftOp instanceof FpLitExpr && rightOp instanceof FpLitExpr) {
            return Bool(!leftOp.equals(rightOp));
        } else if (leftOp instanceof RefExpr && rightOp instanceof RefExpr) {
            if (level != LITERAL_ONLY && leftOp.equals(rightOp)) {
                return False();
            }
        }

        return expr.with(leftOp, rightOp);
    }

    private Expr<FpType> simplifyFpMax(final FpMaxExpr expr, final Valuation val) {
        final Expr<FpType> leftOp = simplify(expr.getLeftOp(), val);
        final Expr<FpType> rightOp = simplify(expr.getRightOp(), val);

        if (leftOp instanceof FpLitExpr && rightOp instanceof FpLitExpr) {
            return expr.eval(val);
        }

        return expr.with(leftOp, rightOp);
    }

    private Expr<FpType> simplifyFpMin(final FpMinExpr expr, final Valuation val) {
        final Expr<FpType> leftOp = simplify(expr.getLeftOp(), val);
        final Expr<FpType> rightOp = simplify(expr.getRightOp(), val);

        if (leftOp instanceof FpLitExpr && rightOp instanceof FpLitExpr) {
            return expr.eval(val);
        }

        return expr.with(leftOp, rightOp);
    }

    private Expr<FpType> simplifyFpSqrt(final FpSqrtExpr expr, final Valuation val) {
        final Expr<FpType> op = simplify(expr.getOp(), val);

        if (op instanceof FpLitExpr) {
            return expr.eval(val);
        }

        return expr.with(op);
    }

    private Expr<FpType> simplifyFpFromBv(final FpFromBvExpr expr, final Valuation val) {
        final Expr<BvType> sgn = simplify(expr.getOp(), val);

        if (sgn instanceof BvLitExpr) {
            return expr.eval(val);
        }

        return expr.with(sgn);
    }

    private Expr<BvType> simplifyFpToBv(final FpToBvExpr expr, final Valuation val) {
        final Expr<FpType> op = simplify(expr.getOp(), val);

        if (op instanceof FpLitExpr) {
            return expr.eval(val);
        }
        return expr.with(op);
    }

    private Expr<FpType> simplifyFpToFp(final FpToFpExpr expr, final Valuation val) {
        final Expr<FpType> op = simplify(expr.getOp(), val);

        if (op instanceof FpLitExpr) {
            return expr.eval(val);
        } else if (op instanceof FpToFpExpr) {
            return simplify(expr.with(((FpToFpExpr) op).getOp()), val);
        }

        return expr.with(op);
    }
}
