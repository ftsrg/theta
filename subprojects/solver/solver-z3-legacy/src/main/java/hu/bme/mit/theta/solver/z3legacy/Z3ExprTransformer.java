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
package hu.bme.mit.theta.solver.z3legacy;

import static com.google.common.base.Preconditions.checkState;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;
import static hu.bme.mit.theta.core.utils.ExprUtils.extractFuncAndArgs;

import com.google.common.cache.Cache;
import com.google.common.cache.CacheBuilder;
import com.microsoft.z3legacy.*;
import hu.bme.mit.theta.common.DispatchTable;
import hu.bme.mit.theta.common.Tuple2;
import hu.bme.mit.theta.common.dsl.Env;
import hu.bme.mit.theta.core.decl.ConstDecl;
import hu.bme.mit.theta.core.decl.Decl;
import hu.bme.mit.theta.core.decl.ParamDecl;
import hu.bme.mit.theta.core.dsl.DeclSymbol;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.anytype.Dereference;
import hu.bme.mit.theta.core.type.anytype.IteExpr;
import hu.bme.mit.theta.core.type.anytype.RefExpr;
import hu.bme.mit.theta.core.type.arraytype.*;
import hu.bme.mit.theta.core.type.booltype.*;
import hu.bme.mit.theta.core.type.bvtype.*;
import hu.bme.mit.theta.core.type.enumtype.EnumEqExpr;
import hu.bme.mit.theta.core.type.enumtype.EnumLitExpr;
import hu.bme.mit.theta.core.type.enumtype.EnumNeqExpr;
import hu.bme.mit.theta.core.type.enumtype.EnumType;
import hu.bme.mit.theta.core.type.fptype.*;
import hu.bme.mit.theta.core.type.functype.FuncAppExpr;
import hu.bme.mit.theta.core.type.functype.FuncType;
import hu.bme.mit.theta.core.type.inttype.*;
import hu.bme.mit.theta.core.type.rattype.*;
import hu.bme.mit.theta.core.utils.BvUtils;
import java.util.List;
import java.util.concurrent.ExecutionException;
import java.util.stream.Stream;

final class Z3ExprTransformer {

    private static final int CACHE_SIZE = 1000;

    private final Z3TransformationManager transformer;
    private final Context context;

    private final Cache<Expr<?>, com.microsoft.z3legacy.Expr> exprToTerm;
    private final DispatchTable<com.microsoft.z3legacy.Expr> table;
    private final Env env;

    public Z3ExprTransformer(final Z3TransformationManager transformer, final Context context) {
        this.context = context;
        this.transformer = transformer;
        this.env = new Env();

        exprToTerm = CacheBuilder.newBuilder().maximumSize(CACHE_SIZE).build();

        table =
                DispatchTable.<com.microsoft.z3legacy.Expr>builder()

                        // General

                        .addCase(RefExpr.class, this::transformRef)
                        .addCase(IteExpr.class, this::transformIte)

                        // Boolean

                        .addCase(FalseExpr.class, this::transformFalse)
                        .addCase(TrueExpr.class, this::transformTrue)
                        .addCase(NotExpr.class, this::transformNot)
                        .addCase(ImplyExpr.class, this::transformImply)
                        .addCase(IffExpr.class, this::transformIff)
                        .addCase(XorExpr.class, this::transformXor)
                        .addCase(AndExpr.class, this::transformAnd)
                        .addCase(OrExpr.class, this::transformOr)
                        .addCase(ExistsExpr.class, this::transformExists)
                        .addCase(ForallExpr.class, this::transformForall)

                        // Rationals

                        .addCase(RatLitExpr.class, this::transformRatLit)
                        .addCase(RatAddExpr.class, this::transformRatAdd)
                        .addCase(RatSubExpr.class, this::transformRatSub)
                        .addCase(RatPosExpr.class, this::transformRatPos)
                        .addCase(RatNegExpr.class, this::transformRatNeg)
                        .addCase(RatMulExpr.class, this::transformRatMul)
                        .addCase(RatDivExpr.class, this::transformRatDiv)
                        .addCase(RatEqExpr.class, this::transformRatEq)
                        .addCase(RatNeqExpr.class, this::transformRatNeq)
                        .addCase(RatGeqExpr.class, this::transformRatGeq)
                        .addCase(RatGtExpr.class, this::transformRatGt)
                        .addCase(RatLeqExpr.class, this::transformRatLeq)
                        .addCase(RatLtExpr.class, this::transformRatLt)
                        .addCase(RatToIntExpr.class, this::transformRatToInt)

                        // Integers

                        .addCase(IntLitExpr.class, this::transformIntLit)
                        .addCase(IntAddExpr.class, this::transformIntAdd)
                        .addCase(IntSubExpr.class, this::transformIntSub)
                        .addCase(IntPosExpr.class, this::transformIntPos)
                        .addCase(IntNegExpr.class, this::transformIntNeg)
                        .addCase(IntMulExpr.class, this::transformIntMul)
                        .addCase(IntDivExpr.class, this::transformIntDiv)
                        .addCase(IntModExpr.class, this::transformIntMod)
                        .addCase(IntRemExpr.class, this::transformIntRem)
                        .addCase(IntEqExpr.class, this::transformIntEq)
                        .addCase(IntNeqExpr.class, this::transformIntNeq)
                        .addCase(IntGeqExpr.class, this::transformIntGeq)
                        .addCase(IntGtExpr.class, this::transformIntGt)
                        .addCase(IntLeqExpr.class, this::transformIntLeq)
                        .addCase(IntLtExpr.class, this::transformIntLt)
                        .addCase(IntToRatExpr.class, this::transformIntToRat)

                        // Bitvectors

                        .addCase(BvLitExpr.class, this::transformBvLit)
                        .addCase(BvConcatExpr.class, this::transformBvConcat)
                        .addCase(BvExtractExpr.class, this::transformBvExtract)
                        .addCase(BvZExtExpr.class, this::transformBvZExt)
                        .addCase(BvSExtExpr.class, this::transformBvSExt)
                        .addCase(BvAddExpr.class, this::transformBvAdd)
                        .addCase(BvSubExpr.class, this::transformBvSub)
                        .addCase(BvPosExpr.class, this::transformBvPos)
                        .addCase(BvToIntExpr.class, this::transformBvToInt)
                        .addCase(BvSignChangeExpr.class, this::transformBvSignChange)
                        .addCase(BvNegExpr.class, this::transformBvNeg)
                        .addCase(BvMulExpr.class, this::transformBvMul)
                        .addCase(BvUDivExpr.class, this::transformBvUDiv)
                        .addCase(BvSDivExpr.class, this::transformBvSDiv)
                        .addCase(BvSModExpr.class, this::transformBvSMod)
                        .addCase(BvURemExpr.class, this::transformBvURem)
                        .addCase(BvSRemExpr.class, this::transformBvSRem)
                        .addCase(BvAndExpr.class, this::transformBvAnd)
                        .addCase(BvOrExpr.class, this::transformBvOr)
                        .addCase(BvXorExpr.class, this::transformBvXor)
                        .addCase(BvNotExpr.class, this::transformBvNot)
                        .addCase(BvShiftLeftExpr.class, this::transformBvShiftLeft)
                        .addCase(BvArithShiftRightExpr.class, this::transformBvArithShiftRight)
                        .addCase(BvLogicShiftRightExpr.class, this::transformBvLogicShiftRight)
                        .addCase(BvRotateLeftExpr.class, this::transformBvRotateLeft)
                        .addCase(BvRotateRightExpr.class, this::transformBvRotateRight)
                        .addCase(BvEqExpr.class, this::transformBvEq)
                        .addCase(BvNeqExpr.class, this::transformBvNeq)
                        .addCase(BvUGeqExpr.class, this::transformBvUGeq)
                        .addCase(BvUGtExpr.class, this::transformBvUGt)
                        .addCase(BvULeqExpr.class, this::transformBvULeq)
                        .addCase(BvULtExpr.class, this::transformBvULt)
                        .addCase(BvSGeqExpr.class, this::transformBvSGeq)
                        .addCase(BvSGtExpr.class, this::transformBvSGt)
                        .addCase(BvSLeqExpr.class, this::transformBvSLeq)
                        .addCase(BvSLtExpr.class, this::transformBvSLt)

                        // Floating points

                        .addCase(FpLitExpr.class, this::transformFpLit)
                        .addCase(FpAddExpr.class, this::transformFpAdd)
                        .addCase(FpSubExpr.class, this::transformFpSub)
                        .addCase(FpPosExpr.class, this::transformFpPos)
                        .addCase(FpNegExpr.class, this::transformFpNeg)
                        .addCase(FpMulExpr.class, this::transformFpMul)
                        .addCase(FpDivExpr.class, this::transformFpDiv)
                        .addCase(FpEqExpr.class, this::transformFpEq)
                        .addCase(FpAssignExpr.class, this::transformFpAssign)
                        .addCase(FpGeqExpr.class, this::transformFpGeq)
                        .addCase(FpLeqExpr.class, this::transformFpLeq)
                        .addCase(FpGtExpr.class, this::transformFpGt)
                        .addCase(FpLtExpr.class, this::transformFpLt)
                        .addCase(FpNeqExpr.class, this::transformFpNeq)
                        .addCase(FpAbsExpr.class, this::transformFpAbs)
                        .addCase(FpRoundToIntegralExpr.class, this::transformFpRoundToIntegral)
                        .addCase(FpMaxExpr.class, this::transformFpMax)
                        .addCase(FpMinExpr.class, this::transformFpMin)
                        .addCase(FpSqrtExpr.class, this::transformFpSqrt)
                        .addCase(FpRemExpr.class, this::transformFpRem)
                        .addCase(FpIsNanExpr.class, this::transformFpIsNan)
                        .addCase(FpIsInfiniteExpr.class, this::transformFpIsInfinite)
                        .addCase(FpFromBvExpr.class, this::transformFpFromBv)
                        .addCase(FpToBvExpr.class, this::transformFpToBv)
                        .addCase(FpToFpExpr.class, this::transformFpToFp)

                        // Functions

                        .addCase(FuncAppExpr.class, this::transformFuncApp)

                        // Arrays

                        .addCase(ArrayReadExpr.class, this::transformArrayRead)
                        .addCase(ArrayWriteExpr.class, this::transformArrayWrite)
                        .addCase(ArrayEqExpr.class, this::transformArrayEq)
                        .addCase(ArrayNeqExpr.class, this::transformArrayNeq)
                        .addCase(ArrayLitExpr.class, this::transformArrayLit)
                        .addCase(ArrayInitExpr.class, this::transformArrayInit)

                        // Dereference

                        .addCase(Dereference.class, this::transformDereference)

                        // Enums

                        .addCase(EnumLitExpr.class, this::transformEnumLit)
                        .addCase(EnumEqExpr.class, this::transformEnumEq)
                        .addCase(EnumNeqExpr.class, this::transformEnumNeq)
                        .build();
    }

    ////

    /*
     * General
     */

    public com.microsoft.z3legacy.Expr toTerm(final Expr<?> expr) {
        try {
            return exprToTerm.get(expr, () -> table.dispatch(expr));
        } catch (final ExecutionException e) {
            throw new AssertionError("Unhandled case: " + expr, e);
        }
    }

    private com.microsoft.z3legacy.Expr transformRef(final RefExpr<?> expr) {
        final Decl<?> decl = expr.getDecl();
        if (decl instanceof ConstDecl) {
            final com.microsoft.z3legacy.FuncDecl funcDecl = transformer.toSymbol(decl);
            return context.mkConst(funcDecl);
        } else if (decl instanceof ParamDecl) {
            final com.microsoft.z3legacy.FuncDecl funcDecl =
                    (com.microsoft.z3legacy.FuncDecl) env.eval(DeclSymbol.of(decl));
            return context.mkConst(funcDecl);
        } else {
            throw new UnsupportedOperationException(
                    "Cannot transform reference for declaration: " + decl);
        }
    }

    /*
     * Booleans
     */

    private com.microsoft.z3legacy.Expr transformIte(final IteExpr<?> expr) {
        final BoolExpr condTerm = (BoolExpr) toTerm(expr.getCond());
        final com.microsoft.z3legacy.Expr thenTerm = toTerm(expr.getThen());
        final com.microsoft.z3legacy.Expr elzeTerm = toTerm(expr.getElse());
        return context.mkITE(condTerm, thenTerm, elzeTerm);
    }

    private com.microsoft.z3legacy.Expr transformFalse(final FalseExpr expr) {
        return context.mkFalse();
    }

    private com.microsoft.z3legacy.Expr transformTrue(final TrueExpr expr) {
        return context.mkTrue();
    }

    private com.microsoft.z3legacy.Expr transformNot(final NotExpr expr) {
        final BoolExpr opTerm = (BoolExpr) toTerm(expr.getOp());
        return context.mkNot(opTerm);
    }

    private com.microsoft.z3legacy.Expr transformImply(final ImplyExpr expr) {
        final BoolExpr leftOpTerm = (BoolExpr) toTerm(expr.getLeftOp());
        final BoolExpr rightOpTerm = (BoolExpr) toTerm(expr.getRightOp());
        return context.mkImplies(leftOpTerm, rightOpTerm);
    }

    private com.microsoft.z3legacy.Expr transformIff(final IffExpr expr) {
        final BoolExpr leftOpTerm = (BoolExpr) toTerm(expr.getLeftOp());
        final BoolExpr rightOpTerm = (BoolExpr) toTerm(expr.getRightOp());
        return context.mkIff(leftOpTerm, rightOpTerm);
    }

    private com.microsoft.z3legacy.Expr transformXor(final XorExpr expr) {
        final BoolExpr leftOpTerm = (BoolExpr) toTerm(expr.getLeftOp());
        final BoolExpr rightOpTerm = (BoolExpr) toTerm(expr.getRightOp());
        return context.mkXor(leftOpTerm, rightOpTerm);
    }

    private com.microsoft.z3legacy.Expr transformAnd(final AndExpr expr) {
        final BoolExpr[] opTerms =
                expr.getOps().stream().map(e -> (BoolExpr) toTerm(e)).toArray(BoolExpr[]::new);
        return context.mkAnd(opTerms);
    }

    private com.microsoft.z3legacy.Expr transformOr(final OrExpr expr) {
        final BoolExpr[] opTerms =
                expr.getOps().stream().map(e -> (BoolExpr) toTerm(e)).toArray(BoolExpr[]::new);
        return context.mkOr(opTerms);
    }

    private com.microsoft.z3legacy.Expr transformExists(final ExistsExpr expr) {
        env.push();
        final com.microsoft.z3legacy.Expr[] paramTerms = transformParamDecls(expr.getParamDecls());
        final BoolExpr opTerm = (BoolExpr) toTerm(expr.getOp());
        final BoolExpr result = context.mkExists(paramTerms, opTerm, 1, null, null, null, null);
        env.pop();
        return result;
    }

    private com.microsoft.z3legacy.Expr transformForall(final ForallExpr expr) {
        env.push();
        final com.microsoft.z3legacy.Expr[] paramTerms = transformParamDecls(expr.getParamDecls());
        final BoolExpr opTerm = (BoolExpr) toTerm(expr.getOp());
        final BoolExpr result = context.mkForall(paramTerms, opTerm, 1, null, null, null, null);
        env.pop();
        return result;
    }

    private com.microsoft.z3legacy.Expr[] transformParamDecls(final List<ParamDecl<?>> paramDecls) {
        final com.microsoft.z3legacy.Expr[] paramTerms =
                new com.microsoft.z3legacy.Expr[paramDecls.size()];
        int i = 0;
        for (final ParamDecl<?> paramDecl : paramDecls) {
            final com.microsoft.z3legacy.FuncDecl paramSymbol = transformParamDecl(paramDecl);
            paramTerms[i] = context.mkConst(paramSymbol);
            env.define(DeclSymbol.of(paramDecl), paramSymbol);
            i++;
        }
        return paramTerms;
    }

    /*
     * Rationals
     */

    private com.microsoft.z3legacy.FuncDecl transformParamDecl(final ParamDecl<?> paramDecl) {
        final Type type = paramDecl.getType();
        if (type instanceof FuncType<?, ?>) {
            throw new UnsupportedOperationException("Only simple types are supported");
        } else {
            final com.microsoft.z3legacy.Sort sort = transformer.toSort(type);
            return context.mkConstDecl(paramDecl.getName(), sort);
        }
    }

    private com.microsoft.z3legacy.Expr transformRatLit(final RatLitExpr expr) {
        var num = context.mkReal(expr.getNum().toString());
        var denom = context.mkReal(expr.getDenom().toString());
        return context.mkDiv(num, denom);
    }

    private com.microsoft.z3legacy.Expr transformRatAdd(final RatAddExpr expr) {
        final com.microsoft.z3legacy.ArithExpr[] opTerms =
                expr.getOps().stream()
                        .map(e -> (com.microsoft.z3legacy.ArithExpr) toTerm(e))
                        .toArray(com.microsoft.z3legacy.ArithExpr[]::new);
        return context.mkAdd(opTerms);
    }

    private com.microsoft.z3legacy.Expr transformRatSub(final RatSubExpr expr) {
        final com.microsoft.z3legacy.ArithExpr leftOpTerm =
                (com.microsoft.z3legacy.ArithExpr) toTerm(expr.getLeftOp());
        final com.microsoft.z3legacy.ArithExpr rightOpTerm =
                (com.microsoft.z3legacy.ArithExpr) toTerm(expr.getRightOp());
        return context.mkSub(leftOpTerm, rightOpTerm);
    }

    private com.microsoft.z3legacy.Expr transformRatPos(final RatPosExpr expr) {
        return toTerm(expr.getOp());
    }

    private com.microsoft.z3legacy.Expr transformRatNeg(final RatNegExpr expr) {
        final com.microsoft.z3legacy.ArithExpr opTerm =
                (com.microsoft.z3legacy.ArithExpr) toTerm(expr.getOp());
        return context.mkUnaryMinus(opTerm);
    }

    private com.microsoft.z3legacy.Expr transformRatMul(final RatMulExpr expr) {
        final com.microsoft.z3legacy.ArithExpr[] opTerms =
                expr.getOps().stream()
                        .map(e -> (com.microsoft.z3legacy.ArithExpr) toTerm(e))
                        .toArray(com.microsoft.z3legacy.ArithExpr[]::new);
        return context.mkMul(opTerms);
    }

    private com.microsoft.z3legacy.Expr transformRatDiv(final RatDivExpr expr) {
        final com.microsoft.z3legacy.ArithExpr leftOpTerm =
                (com.microsoft.z3legacy.ArithExpr) toTerm(expr.getLeftOp());
        final com.microsoft.z3legacy.ArithExpr rightOpTerm =
                (com.microsoft.z3legacy.ArithExpr) toTerm(expr.getRightOp());
        return context.mkDiv(leftOpTerm, rightOpTerm);
    }

    private com.microsoft.z3legacy.Expr transformRatEq(final RatEqExpr expr) {
        final com.microsoft.z3legacy.Expr leftOpTerm = toTerm(expr.getLeftOp());
        final com.microsoft.z3legacy.Expr rightOpTerm = toTerm(expr.getRightOp());
        return context.mkEq(leftOpTerm, rightOpTerm);
    }

    private com.microsoft.z3legacy.Expr transformRatNeq(final RatNeqExpr expr) {
        final com.microsoft.z3legacy.Expr leftOpTerm = toTerm(expr.getLeftOp());
        final com.microsoft.z3legacy.Expr rightOpTerm = toTerm(expr.getRightOp());
        return context.mkNot(context.mkEq(leftOpTerm, rightOpTerm));
    }

    private com.microsoft.z3legacy.Expr transformRatGeq(final RatGeqExpr expr) {
        final com.microsoft.z3legacy.ArithExpr leftOpTerm =
                (com.microsoft.z3legacy.ArithExpr) toTerm(expr.getLeftOp());
        final com.microsoft.z3legacy.ArithExpr rightOpTerm =
                (com.microsoft.z3legacy.ArithExpr) toTerm(expr.getRightOp());
        return context.mkGe(leftOpTerm, rightOpTerm);
    }

    private com.microsoft.z3legacy.Expr transformRatGt(final RatGtExpr expr) {
        final com.microsoft.z3legacy.ArithExpr leftOpTerm =
                (com.microsoft.z3legacy.ArithExpr) toTerm(expr.getLeftOp());
        final com.microsoft.z3legacy.ArithExpr rightOpTerm =
                (com.microsoft.z3legacy.ArithExpr) toTerm(expr.getRightOp());
        return context.mkGt(leftOpTerm, rightOpTerm);
    }

    private com.microsoft.z3legacy.Expr transformRatLeq(final RatLeqExpr expr) {
        final com.microsoft.z3legacy.ArithExpr leftOpTerm =
                (com.microsoft.z3legacy.ArithExpr) toTerm(expr.getLeftOp());
        final com.microsoft.z3legacy.ArithExpr rightOpTerm =
                (com.microsoft.z3legacy.ArithExpr) toTerm(expr.getRightOp());
        return context.mkLe(leftOpTerm, rightOpTerm);
    }

    private com.microsoft.z3legacy.Expr transformRatLt(final RatLtExpr expr) {
        final com.microsoft.z3legacy.ArithExpr leftOpTerm =
                (com.microsoft.z3legacy.ArithExpr) toTerm(expr.getLeftOp());
        final com.microsoft.z3legacy.ArithExpr rightOpTerm =
                (com.microsoft.z3legacy.ArithExpr) toTerm(expr.getRightOp());
        return context.mkLt(leftOpTerm, rightOpTerm);
    }

    /*
     * Integers
     */

    private com.microsoft.z3legacy.Expr transformRatToInt(final RatToIntExpr expr) {
        final com.microsoft.z3legacy.RealExpr opTerm =
                (com.microsoft.z3legacy.RealExpr) toTerm(expr.getOp());
        return context.mkReal2Int(opTerm);
    }

    private com.microsoft.z3legacy.Expr transformIntLit(final IntLitExpr expr) {
        return context.mkInt(expr.getValue().toString());
    }

    private com.microsoft.z3legacy.Expr transformIntAdd(final IntAddExpr expr) {
        final com.microsoft.z3legacy.ArithExpr[] opTerms =
                expr.getOps().stream()
                        .map(e -> (com.microsoft.z3legacy.ArithExpr) toTerm(e))
                        .toArray(com.microsoft.z3legacy.ArithExpr[]::new);
        return context.mkAdd(opTerms);
    }

    private com.microsoft.z3legacy.Expr transformIntSub(final IntSubExpr expr) {
        final com.microsoft.z3legacy.ArithExpr leftOpTerm =
                (com.microsoft.z3legacy.ArithExpr) toTerm(expr.getLeftOp());
        final com.microsoft.z3legacy.ArithExpr rightOpTerm =
                (com.microsoft.z3legacy.ArithExpr) toTerm(expr.getRightOp());
        return context.mkSub(leftOpTerm, rightOpTerm);
    }

    private com.microsoft.z3legacy.Expr transformIntPos(final IntPosExpr expr) {
        return toTerm(expr.getOp());
    }

    private com.microsoft.z3legacy.Expr transformIntNeg(final IntNegExpr expr) {
        final com.microsoft.z3legacy.ArithExpr opTerm =
                (com.microsoft.z3legacy.ArithExpr) toTerm(expr.getOp());
        return context.mkUnaryMinus(opTerm);
    }

    private com.microsoft.z3legacy.Expr transformIntMul(final IntMulExpr expr) {
        final com.microsoft.z3legacy.ArithExpr[] opTerms =
                expr.getOps().stream()
                        .map(e -> (com.microsoft.z3legacy.ArithExpr) toTerm(e))
                        .toArray(com.microsoft.z3legacy.ArithExpr[]::new);
        return context.mkMul(opTerms);
    }

    private com.microsoft.z3legacy.Expr transformIntDiv(final IntDivExpr expr) {
        final com.microsoft.z3legacy.IntExpr leftOpTerm =
                (com.microsoft.z3legacy.IntExpr) toTerm(expr.getLeftOp());
        final com.microsoft.z3legacy.IntExpr rightOpTerm =
                (com.microsoft.z3legacy.IntExpr) toTerm(expr.getRightOp());
        return context.mkDiv(leftOpTerm, rightOpTerm);
    }

    private com.microsoft.z3legacy.Expr transformIntMod(final IntModExpr expr) {
        final com.microsoft.z3legacy.IntExpr leftOpTerm =
                (com.microsoft.z3legacy.IntExpr) toTerm(expr.getLeftOp());
        final com.microsoft.z3legacy.IntExpr rightOpTerm =
                (com.microsoft.z3legacy.IntExpr) toTerm(expr.getRightOp());
        return context.mkMod(leftOpTerm, rightOpTerm);
    }

    private com.microsoft.z3legacy.Expr transformIntRem(final IntRemExpr expr) {
        final com.microsoft.z3legacy.IntExpr leftOpTerm =
                (com.microsoft.z3legacy.IntExpr) toTerm(expr.getLeftOp());
        final com.microsoft.z3legacy.IntExpr rightOpTerm =
                (com.microsoft.z3legacy.IntExpr) toTerm(expr.getRightOp());
        return context.mkRem(leftOpTerm, rightOpTerm);
    }

    private com.microsoft.z3legacy.Expr transformIntEq(final IntEqExpr expr) {
        final com.microsoft.z3legacy.Expr leftOpTerm = toTerm(expr.getLeftOp());
        final com.microsoft.z3legacy.Expr rightOpTerm = toTerm(expr.getRightOp());
        return context.mkEq(leftOpTerm, rightOpTerm);
    }

    private com.microsoft.z3legacy.Expr transformIntNeq(final IntNeqExpr expr) {
        final com.microsoft.z3legacy.Expr leftOpTerm = toTerm(expr.getLeftOp());
        final com.microsoft.z3legacy.Expr rightOpTerm = toTerm(expr.getRightOp());
        return context.mkNot(context.mkEq(leftOpTerm, rightOpTerm));
    }

    private com.microsoft.z3legacy.Expr transformIntGeq(final IntGeqExpr expr) {
        final com.microsoft.z3legacy.ArithExpr leftOpTerm =
                (com.microsoft.z3legacy.ArithExpr) toTerm(expr.getLeftOp());
        final com.microsoft.z3legacy.ArithExpr rightOpTerm =
                (com.microsoft.z3legacy.ArithExpr) toTerm(expr.getRightOp());
        return context.mkGe(leftOpTerm, rightOpTerm);
    }

    private com.microsoft.z3legacy.Expr transformIntGt(final IntGtExpr expr) {
        final com.microsoft.z3legacy.ArithExpr leftOpTerm =
                (com.microsoft.z3legacy.ArithExpr) toTerm(expr.getLeftOp());
        final com.microsoft.z3legacy.ArithExpr rightOpTerm =
                (com.microsoft.z3legacy.ArithExpr) toTerm(expr.getRightOp());
        return context.mkGt(leftOpTerm, rightOpTerm);
    }

    private com.microsoft.z3legacy.Expr transformIntLeq(final IntLeqExpr expr) {
        final com.microsoft.z3legacy.ArithExpr leftOpTerm =
                (com.microsoft.z3legacy.ArithExpr) toTerm(expr.getLeftOp());
        final com.microsoft.z3legacy.ArithExpr rightOpTerm =
                (com.microsoft.z3legacy.ArithExpr) toTerm(expr.getRightOp());
        return context.mkLe(leftOpTerm, rightOpTerm);
    }

    private com.microsoft.z3legacy.Expr transformIntLt(final IntLtExpr expr) {
        final com.microsoft.z3legacy.ArithExpr leftOpTerm =
                (com.microsoft.z3legacy.ArithExpr) toTerm(expr.getLeftOp());
        final com.microsoft.z3legacy.ArithExpr rightOpTerm =
                (com.microsoft.z3legacy.ArithExpr) toTerm(expr.getRightOp());
        return context.mkLt(leftOpTerm, rightOpTerm);
    }

    /*
     * Bitvectors
     */

    private com.microsoft.z3legacy.Expr transformIntToRat(final IntToRatExpr expr) {
        final com.microsoft.z3legacy.IntExpr opTerm =
                (com.microsoft.z3legacy.IntExpr) toTerm(expr.getOp());
        return context.mkInt2Real(opTerm);
    }

    private com.microsoft.z3legacy.Expr transformBvLit(final BvLitExpr expr) {
        return context.mkBV(
                BvUtils.neutralBvLitExprToBigInteger(expr).toString(), expr.getType().getSize());
    }

    private com.microsoft.z3legacy.Expr transformBvEq(final BvEqExpr expr) {
        final com.microsoft.z3legacy.Expr leftOpTerm = toTerm(expr.getLeftOp());
        final com.microsoft.z3legacy.Expr rightOpTerm = toTerm(expr.getRightOp());
        return context.mkEq(leftOpTerm, rightOpTerm);
    }

    private com.microsoft.z3legacy.Expr transformBvNeq(final BvNeqExpr expr) {
        final com.microsoft.z3legacy.Expr leftOpTerm = toTerm(expr.getLeftOp());
        final com.microsoft.z3legacy.Expr rightOpTerm = toTerm(expr.getRightOp());
        return context.mkNot(context.mkEq(leftOpTerm, rightOpTerm));
    }

    private com.microsoft.z3legacy.Expr transformBvConcat(final BvConcatExpr expr) {
        final BitVecExpr[] opTerms =
                expr.getOps().stream().map(e -> (BitVecExpr) toTerm(e)).toArray(BitVecExpr[]::new);

        return Stream.of(opTerms).skip(1).reduce(opTerms[0], context::mkConcat);
    }

    private com.microsoft.z3legacy.Expr transformBvExtract(final BvExtractExpr expr) {
        final BitVecExpr bitvecTerm = (BitVecExpr) toTerm(expr.getBitvec());
        final int from = expr.getFrom().getValue().intValue();
        final int until = expr.getUntil().getValue().intValue();

        return context.mkExtract(until - 1, from, bitvecTerm);
    }

    private com.microsoft.z3legacy.Expr transformBvZExt(final BvZExtExpr expr) {
        final BitVecExpr bitvecTerm = (BitVecExpr) toTerm(expr.getOp());
        final int extendWith = expr.getExtendType().getSize() - expr.getOp().getType().getSize();

        return context.mkZeroExt(extendWith, bitvecTerm);
    }

    private com.microsoft.z3legacy.Expr transformBvSExt(final BvSExtExpr expr) {
        final BitVecExpr bitvecTerm = (BitVecExpr) toTerm(expr.getOp());
        final int extendWith = expr.getExtendType().getSize() - expr.getOp().getType().getSize();

        return context.mkSignExt(extendWith, bitvecTerm);
    }

    private com.microsoft.z3legacy.Expr transformBvAdd(final BvAddExpr expr) {
        final BitVecExpr[] opTerms =
                expr.getOps().stream().map(e -> (BitVecExpr) toTerm(e)).toArray(BitVecExpr[]::new);

        return Stream.of(opTerms).skip(1).reduce(opTerms[0], context::mkBVAdd);
    }

    private com.microsoft.z3legacy.Expr transformBvSub(final BvSubExpr expr) {
        final BitVecExpr leftOpTerm = (BitVecExpr) toTerm(expr.getLeftOp());
        final BitVecExpr rightOpTerm = (BitVecExpr) toTerm(expr.getRightOp());
        return context.mkBVSub(leftOpTerm, rightOpTerm);
    }

    private com.microsoft.z3legacy.Expr transformBvPos(final BvPosExpr expr) {
        return toTerm(expr.getOp());
    }

    private com.microsoft.z3legacy.Expr transformBvToInt(final BvToIntExpr expr) {
        return context.mkBV2Int((BitVecExpr) toTerm(expr.getOp()), expr.isSigned());
    }

    private com.microsoft.z3legacy.Expr transformBvSignChange(final BvSignChangeExpr expr) {
        return toTerm(expr.getOp());
    }

    private com.microsoft.z3legacy.Expr transformBvNeg(final BvNegExpr expr) {
        final BitVecExpr opTerm = (BitVecExpr) toTerm(expr.getOp());
        return context.mkBVNeg(opTerm);
    }

    private com.microsoft.z3legacy.Expr transformBvMul(final BvMulExpr expr) {
        final BitVecExpr[] opTerms =
                expr.getOps().stream().map(e -> (BitVecExpr) toTerm(e)).toArray(BitVecExpr[]::new);

        return Stream.of(opTerms).skip(1).reduce(opTerms[0], context::mkBVMul);
    }

    private com.microsoft.z3legacy.Expr transformBvUDiv(final BvUDivExpr expr) {
        final BitVecExpr leftOpTerm = (BitVecExpr) toTerm(expr.getLeftOp());
        final BitVecExpr rightOpTerm = (BitVecExpr) toTerm(expr.getRightOp());

        return context.mkBVUDiv(leftOpTerm, rightOpTerm);
    }

    private com.microsoft.z3legacy.Expr transformBvSDiv(final BvSDivExpr expr) {
        final BitVecExpr leftOpTerm = (BitVecExpr) toTerm(expr.getLeftOp());
        final BitVecExpr rightOpTerm = (BitVecExpr) toTerm(expr.getRightOp());

        return context.mkBVSDiv(leftOpTerm, rightOpTerm);
    }

    private com.microsoft.z3legacy.Expr transformBvSMod(final BvSModExpr expr) {
        final BitVecExpr leftOpTerm = (BitVecExpr) toTerm(expr.getLeftOp());
        final BitVecExpr rightOpTerm = (BitVecExpr) toTerm(expr.getRightOp());

        return context.mkBVSMod(leftOpTerm, rightOpTerm);
    }

    private com.microsoft.z3legacy.Expr transformBvURem(final BvURemExpr expr) {
        final BitVecExpr leftOpTerm = (BitVecExpr) toTerm(expr.getLeftOp());
        final BitVecExpr rightOpTerm = (BitVecExpr) toTerm(expr.getRightOp());

        return context.mkBVURem(leftOpTerm, rightOpTerm);
    }

    private com.microsoft.z3legacy.Expr transformBvSRem(final BvSRemExpr expr) {
        final BitVecExpr leftOpTerm = (BitVecExpr) toTerm(expr.getLeftOp());
        final BitVecExpr rightOpTerm = (BitVecExpr) toTerm(expr.getRightOp());

        return context.mkBVSRem(leftOpTerm, rightOpTerm);
    }

    private com.microsoft.z3legacy.Expr transformBvAnd(final BvAndExpr expr) {
        final BitVecExpr[] opTerms =
                expr.getOps().stream().map(e -> (BitVecExpr) toTerm(e)).toArray(BitVecExpr[]::new);

        return Stream.of(opTerms).skip(1).reduce(opTerms[0], context::mkBVAND);
    }

    private com.microsoft.z3legacy.Expr transformBvOr(final BvOrExpr expr) {
        final BitVecExpr[] opTerms =
                expr.getOps().stream().map(e -> (BitVecExpr) toTerm(e)).toArray(BitVecExpr[]::new);

        return Stream.of(opTerms).skip(1).reduce(opTerms[0], context::mkBVOR);
    }

    private com.microsoft.z3legacy.Expr transformBvXor(final BvXorExpr expr) {
        final BitVecExpr[] opTerms =
                expr.getOps().stream().map(e -> (BitVecExpr) toTerm(e)).toArray(BitVecExpr[]::new);

        return Stream.of(opTerms).skip(1).reduce(opTerms[0], context::mkBVXOR);
    }

    private com.microsoft.z3legacy.Expr transformBvNot(final BvNotExpr expr) {
        final BitVecExpr opTerm = (BitVecExpr) toTerm(expr.getOp());

        return context.mkBVNot(opTerm);
    }

    private com.microsoft.z3legacy.Expr transformBvShiftLeft(final BvShiftLeftExpr expr) {
        final BitVecExpr leftOpTerm = (BitVecExpr) toTerm(expr.getLeftOp());
        final BitVecExpr rightOpTerm = (BitVecExpr) toTerm(expr.getRightOp());

        return context.mkBVSHL(leftOpTerm, rightOpTerm);
    }

    private com.microsoft.z3legacy.Expr transformBvArithShiftRight(
            final BvArithShiftRightExpr expr) {
        final BitVecExpr leftOpTerm = (BitVecExpr) toTerm(expr.getLeftOp());
        final BitVecExpr rightOpTerm = (BitVecExpr) toTerm(expr.getRightOp());

        return context.mkBVASHR(leftOpTerm, rightOpTerm);
    }

    private com.microsoft.z3legacy.Expr transformBvLogicShiftRight(
            final BvLogicShiftRightExpr expr) {
        final BitVecExpr leftOpTerm = (BitVecExpr) toTerm(expr.getLeftOp());
        final BitVecExpr rightOpTerm = (BitVecExpr) toTerm(expr.getRightOp());

        return context.mkBVLSHR(leftOpTerm, rightOpTerm);
    }

    private com.microsoft.z3legacy.Expr transformBvRotateLeft(final BvRotateLeftExpr expr) {
        final BitVecExpr leftOpTerm = (BitVecExpr) toTerm(expr.getLeftOp());
        final BitVecExpr rightOpTerm = (BitVecExpr) toTerm(expr.getRightOp());

        return context.mkBVRotateLeft(leftOpTerm, rightOpTerm);
    }

    private com.microsoft.z3legacy.Expr transformBvRotateRight(final BvRotateRightExpr expr) {
        final BitVecExpr leftOpTerm = (BitVecExpr) toTerm(expr.getLeftOp());
        final BitVecExpr rightOpTerm = (BitVecExpr) toTerm(expr.getRightOp());

        return context.mkBVRotateRight(leftOpTerm, rightOpTerm);
    }

    private com.microsoft.z3legacy.Expr transformBvUGeq(final BvUGeqExpr expr) {
        final BitVecExpr leftOpTerm = (BitVecExpr) toTerm(expr.getLeftOp());
        final BitVecExpr rightOpTerm = (BitVecExpr) toTerm(expr.getRightOp());

        return context.mkBVUGE(leftOpTerm, rightOpTerm);
    }

    private com.microsoft.z3legacy.Expr transformBvUGt(final BvUGtExpr expr) {
        final BitVecExpr leftOpTerm = (BitVecExpr) toTerm(expr.getLeftOp());
        final BitVecExpr rightOpTerm = (BitVecExpr) toTerm(expr.getRightOp());

        return context.mkBVUGT(leftOpTerm, rightOpTerm);
    }

    private com.microsoft.z3legacy.Expr transformBvULeq(final BvULeqExpr expr) {
        final BitVecExpr leftOpTerm = (BitVecExpr) toTerm(expr.getLeftOp());
        final BitVecExpr rightOpTerm = (BitVecExpr) toTerm(expr.getRightOp());

        return context.mkBVULE(leftOpTerm, rightOpTerm);
    }

    private com.microsoft.z3legacy.Expr transformBvULt(final BvULtExpr expr) {
        final BitVecExpr leftOpTerm = (BitVecExpr) toTerm(expr.getLeftOp());
        final BitVecExpr rightOpTerm = (BitVecExpr) toTerm(expr.getRightOp());

        return context.mkBVULT(leftOpTerm, rightOpTerm);
    }

    private com.microsoft.z3legacy.Expr transformBvSGeq(final BvSGeqExpr expr) {
        final BitVecExpr leftOpTerm = (BitVecExpr) toTerm(expr.getLeftOp());
        final BitVecExpr rightOpTerm = (BitVecExpr) toTerm(expr.getRightOp());

        return context.mkBVSGE(leftOpTerm, rightOpTerm);
    }

    private com.microsoft.z3legacy.Expr transformBvSGt(final BvSGtExpr expr) {
        final BitVecExpr leftOpTerm = (BitVecExpr) toTerm(expr.getLeftOp());
        final BitVecExpr rightOpTerm = (BitVecExpr) toTerm(expr.getRightOp());

        return context.mkBVSGT(leftOpTerm, rightOpTerm);
    }

    private com.microsoft.z3legacy.Expr transformBvSLeq(final BvSLeqExpr expr) {
        final BitVecExpr leftOpTerm = (BitVecExpr) toTerm(expr.getLeftOp());
        final BitVecExpr rightOpTerm = (BitVecExpr) toTerm(expr.getRightOp());

        return context.mkBVSLE(leftOpTerm, rightOpTerm);
    }

    /*
     * Floating points
     */

    private com.microsoft.z3legacy.Expr transformBvSLt(final BvSLtExpr expr) {
        final BitVecExpr leftOpTerm = (BitVecExpr) toTerm(expr.getLeftOp());
        final BitVecExpr rightOpTerm = (BitVecExpr) toTerm(expr.getRightOp());

        return context.mkBVSLT(leftOpTerm, rightOpTerm);
    }

    private com.microsoft.z3legacy.Expr transformFpLit(final FpLitExpr expr) {
        return context.mkFP(
                context.mkBV(expr.getHidden() ? 1 : 0, 1),
                (BitVecExpr) toTerm(expr.getExponent()),
                (BitVecExpr) toTerm(expr.getSignificand()));
    }

    private com.microsoft.z3legacy.Expr transformFpAdd(final FpAddExpr expr) {
        final FPExpr[] opTerms =
                expr.getOps().stream().map(e -> (FPExpr) toTerm(e)).toArray(FPExpr[]::new);

        return Stream.of(opTerms)
                .skip(1)
                .reduce(
                        opTerms[0],
                        (op1, op2) ->
                                context.mkFPAdd(
                                        transformFpRoundingMode(expr.getRoundingMode()), op1, op2));
    }

    private com.microsoft.z3legacy.Expr transformFpSub(final FpSubExpr expr) {
        final FPExpr leftOpTerm = (FPExpr) toTerm(expr.getLeftOp());
        final FPExpr rightOpTerm = (FPExpr) toTerm(expr.getRightOp());
        return context.mkFPSub(
                transformFpRoundingMode(expr.getRoundingMode()), leftOpTerm, rightOpTerm);
    }

    private com.microsoft.z3legacy.Expr transformFpPos(final FpPosExpr expr) {
        return toTerm(expr.getOp());
    }

    private com.microsoft.z3legacy.Expr transformFpNeg(final FpNegExpr expr) {
        final FPExpr opTerm = (FPExpr) toTerm(expr.getOp());
        return context.mkFPNeg(opTerm);
    }

    private com.microsoft.z3legacy.Expr transformFpAbs(final FpAbsExpr expr) {
        final FPExpr opTerm = (FPExpr) toTerm(expr.getOp());
        return context.mkFPAbs(opTerm);
    }

    private com.microsoft.z3legacy.Expr transformFpIsNan(final FpIsNanExpr expr) {
        final FPExpr opTerm = (FPExpr) toTerm(expr.getOp());
        return context.mkFPIsNaN(opTerm);
    }

    private com.microsoft.z3legacy.Expr transformFpIsInfinite(final FpIsInfiniteExpr expr) {
        final FPExpr opTerm = (FPExpr) toTerm(expr.getOp());
        return context.mkFPIsInfinite(opTerm);
    }

    private com.microsoft.z3legacy.Expr transformFpSqrt(final FpSqrtExpr expr) {
        final FPExpr opTerm = (FPExpr) toTerm(expr.getOp());
        return context.mkFPSqrt(transformFpRoundingMode(expr.getRoundingMode()), opTerm);
    }

    private com.microsoft.z3legacy.Expr transformFpRoundToIntegral(
            final FpRoundToIntegralExpr expr) {
        final FPExpr opTerm = (FPExpr) toTerm(expr.getOp());
        return context.mkFPRoundToIntegral(transformFpRoundingMode(expr.getRoundingMode()), opTerm);
    }

    private com.microsoft.z3legacy.Expr transformFpMul(final FpMulExpr expr) {
        final FPExpr[] opTerms =
                expr.getOps().stream().map(e -> (FPExpr) toTerm(e)).toArray(FPExpr[]::new);

        return Stream.of(opTerms)
                .skip(1)
                .reduce(
                        opTerms[0],
                        (op1, op2) ->
                                context.mkFPMul(
                                        transformFpRoundingMode(expr.getRoundingMode()), op1, op2));
    }

    private com.microsoft.z3legacy.Expr transformFpDiv(final FpDivExpr expr) {
        final FPExpr leftOpTerm = (FPExpr) toTerm(expr.getLeftOp());
        final FPExpr rightOpTerm = (FPExpr) toTerm(expr.getRightOp());

        return context.mkFPDiv(
                transformFpRoundingMode(expr.getRoundingMode()), leftOpTerm, rightOpTerm);
    }

    private com.microsoft.z3legacy.Expr transformFpRem(final FpRemExpr expr) {
        final FPExpr leftOpTerm = (FPExpr) toTerm(expr.getLeftOp());
        final FPExpr rightOpTerm = (FPExpr) toTerm(expr.getRightOp());
        return context.mkFPRem(leftOpTerm, rightOpTerm);
    }

    private com.microsoft.z3legacy.Expr transformFpEq(final FpEqExpr expr) {
        final com.microsoft.z3legacy.Expr leftOpTerm = toTerm(expr.getLeftOp());
        final com.microsoft.z3legacy.Expr rightOpTerm = toTerm(expr.getRightOp());
        return context.mkFPEq((FPExpr) leftOpTerm, (FPExpr) rightOpTerm);
    }

    private com.microsoft.z3legacy.Expr transformFpAssign(final FpAssignExpr expr) {
        final com.microsoft.z3legacy.Expr leftOpTerm = toTerm(expr.getLeftOp());
        final com.microsoft.z3legacy.Expr rightOpTerm = toTerm(expr.getRightOp());
        return context.mkEq(leftOpTerm, rightOpTerm);
    }

    private com.microsoft.z3legacy.Expr transformFpNeq(final FpNeqExpr expr) {
        final com.microsoft.z3legacy.Expr leftOpTerm = toTerm(expr.getLeftOp());
        final com.microsoft.z3legacy.Expr rightOpTerm = toTerm(expr.getRightOp());
        return context.mkNot(context.mkFPEq((FPExpr) leftOpTerm, (FPExpr) rightOpTerm));
    }

    private com.microsoft.z3legacy.Expr transformFpGeq(final FpGeqExpr expr) {
        final com.microsoft.z3legacy.Expr leftOpTerm = toTerm(expr.getLeftOp());
        final com.microsoft.z3legacy.Expr rightOpTerm = toTerm(expr.getRightOp());
        return context.mkFPGEq((FPExpr) leftOpTerm, (FPExpr) rightOpTerm);
    }

    private com.microsoft.z3legacy.Expr transformFpLeq(final FpLeqExpr expr) {
        final com.microsoft.z3legacy.Expr leftOpTerm = toTerm(expr.getLeftOp());
        final com.microsoft.z3legacy.Expr rightOpTerm = toTerm(expr.getRightOp());
        return context.mkFPLEq((FPExpr) leftOpTerm, (FPExpr) rightOpTerm);
    }

    private com.microsoft.z3legacy.Expr transformFpGt(final FpGtExpr expr) {
        final com.microsoft.z3legacy.Expr leftOpTerm = toTerm(expr.getLeftOp());
        final com.microsoft.z3legacy.Expr rightOpTerm = toTerm(expr.getRightOp());
        return context.mkFPGt((FPExpr) leftOpTerm, (FPExpr) rightOpTerm);
    }

    private com.microsoft.z3legacy.Expr transformFpLt(final FpLtExpr expr) {
        final com.microsoft.z3legacy.Expr leftOpTerm = toTerm(expr.getLeftOp());
        final com.microsoft.z3legacy.Expr rightOpTerm = toTerm(expr.getRightOp());
        return context.mkFPLt((FPExpr) leftOpTerm, (FPExpr) rightOpTerm);
    }

    private com.microsoft.z3legacy.FPRMExpr transformFpRoundingMode(
            final FpRoundingMode roundingMode) {
        switch (roundingMode) {
            case RNE:
                return context.mkFPRoundNearestTiesToEven();
            case RNA:
                return context.mkFPRoundNearestTiesToAway();
            case RTP:
                return context.mkFPRoundTowardPositive();
            case RTN:
                return context.mkFPRoundTowardNegative();
            case RTZ:
                return context.mkFPRoundTowardZero();
            default:
                throw new UnsupportedOperationException();
        }
    }

    private com.microsoft.z3legacy.Expr transformFpMax(final FpMaxExpr expr) {
        final FPExpr leftOpTerm = (FPExpr) toTerm(expr.getLeftOp());
        final FPExpr rightOpTerm = (FPExpr) toTerm(expr.getRightOp());
        return context.mkFPMax(leftOpTerm, rightOpTerm);
    }

    private com.microsoft.z3legacy.Expr transformFpMin(final FpMinExpr expr) {
        final FPExpr leftOpTerm = (FPExpr) toTerm(expr.getLeftOp());
        final FPExpr rightOpTerm = (FPExpr) toTerm(expr.getRightOp());
        return context.mkFPMin(leftOpTerm, rightOpTerm);
    }

    private com.microsoft.z3legacy.Expr transformFpFromBv(final FpFromBvExpr expr) {
        final BitVecExpr val = (BitVecExpr) toTerm(expr.getOp());
        final FPSort fpSort =
                context.mkFPSort(expr.getFpType().getExponent(), expr.getFpType().getSignificand());
        return context.mkFPToFP(
                transformFpRoundingMode(expr.getRoundingMode()),
                val,
                fpSort,
                expr.isSigned()); // TODO: is this OK? FP2FP when BV2FP is used?
    }

    private com.microsoft.z3legacy.Expr transformFpToBv(final FpToBvExpr expr) {
        boolean sgn = expr.getSgn();
        int size = expr.getSize();
        final FPExpr op = (FPExpr) toTerm(expr.getOp());

        return context.mkFPToBV(transformFpRoundingMode(expr.getRoundingMode()), op, size, sgn);
    }

    /*
     * Arrays
     */

    private com.microsoft.z3legacy.Expr transformFpToFp(final FpToFpExpr expr) {
        final FPExpr op = (FPExpr) toTerm(expr.getOp());

        return context.mkFPToFP(
                transformFpRoundingMode(expr.getRoundingMode()),
                op,
                new FPSort(context, expr.getExpBits(), expr.getSignBits()));
    }

    private com.microsoft.z3legacy.Expr transformArrayRead(final ArrayReadExpr<?, ?> expr) {
        final com.microsoft.z3legacy.ArrayExpr arrayTerm =
                (com.microsoft.z3legacy.ArrayExpr) toTerm(expr.getArray());
        final com.microsoft.z3legacy.Expr indexTerm = toTerm(expr.getIndex());
        return context.mkSelect(arrayTerm, indexTerm);
    }

    private com.microsoft.z3legacy.Expr transformArrayWrite(final ArrayWriteExpr<?, ?> expr) {
        final com.microsoft.z3legacy.ArrayExpr arrayTerm =
                (com.microsoft.z3legacy.ArrayExpr) toTerm(expr.getArray());
        final com.microsoft.z3legacy.Expr indexTerm = toTerm(expr.getIndex());
        final com.microsoft.z3legacy.Expr elemTerm = toTerm(expr.getElem());
        return context.mkStore(arrayTerm, indexTerm, elemTerm);
    }

    private com.microsoft.z3legacy.Expr transformArrayEq(final ArrayEqExpr<?, ?> expr) {
        final com.microsoft.z3legacy.Expr leftOpTerm = toTerm(expr.getLeftOp());
        final com.microsoft.z3legacy.Expr rightOpTerm = toTerm(expr.getRightOp());
        return context.mkEq(leftOpTerm, rightOpTerm);
    }

    private com.microsoft.z3legacy.Expr transformArrayNeq(final ArrayNeqExpr<?, ?> expr) {
        final com.microsoft.z3legacy.Expr leftOpTerm = toTerm(expr.getLeftOp());
        final com.microsoft.z3legacy.Expr rightOpTerm = toTerm(expr.getRightOp());
        return context.mkNot(context.mkEq(leftOpTerm, rightOpTerm));
    }

    /*
     * Functions
     */

    private com.microsoft.z3legacy.Expr transformArrayLit(final ArrayLitExpr<?, ?> expr) {
        com.microsoft.z3legacy.ArrayExpr running =
                context.mkConstArray(
                        transformer.toSort(expr.getType().getIndexType()),
                        toTerm(expr.getElseElem()));
        for (Tuple2<? extends Expr<?>, ? extends Expr<?>> elem : expr.getElements()) {
            running = context.mkStore(running, toTerm(elem.get1()), toTerm(elem.get2()));
        }
        return running;
    }

    private com.microsoft.z3legacy.Expr transformArrayInit(final ArrayInitExpr<?, ?> expr) {
        com.microsoft.z3legacy.ArrayExpr running =
                context.mkConstArray(
                        transformer.toSort(expr.getType().getIndexType()),
                        toTerm(expr.getElseElem()));
        for (Tuple2<? extends Expr<?>, ? extends Expr<?>> elem : expr.getElements()) {
            running = context.mkStore(running, toTerm(elem.get1()), toTerm(elem.get2()));
        }
        return running;
    }

    private com.microsoft.z3legacy.Expr transformFuncApp(final FuncAppExpr<?, ?> expr) {
        final Tuple2<Expr<?>, List<Expr<?>>> funcAndArgs = extractFuncAndArgs(expr);
        final Expr<?> func = funcAndArgs.get1();
        if (func instanceof RefExpr) {
            final RefExpr<?> ref = (RefExpr<?>) func;
            final Decl<?> decl = ref.getDecl();
            final com.microsoft.z3legacy.FuncDecl funcDecl = transformer.toSymbol(decl);
            final List<Expr<?>> args = funcAndArgs.get2();
            final com.microsoft.z3legacy.Expr[] argTerms =
                    args.stream().map(this::toTerm).toArray(com.microsoft.z3legacy.Expr[]::new);
            return context.mkApp(funcDecl, argTerms);
        } else {
            throw new UnsupportedOperationException(
                    "Higher order functions are not supported: " + func);
        }
    }

    private com.microsoft.z3legacy.Expr transformDereference(final Dereference<?, ?, ?> expr) {
        checkState(
                expr.getUniquenessIdx().isPresent(),
                "Incomplete dereferences (missing uniquenessIdx) are not handled properly.");
        final var sort = transformer.toSort(expr.getArray().getType());
        final var constSort = transformer.toSort(Int());
        final var func =
                context.mkFuncDecl(
                        "deref",
                        new Sort[] {sort, sort, constSort},
                        transformer.toSort(expr.getType()));
        return context.mkApp(
                func,
                toTerm(expr.getArray()),
                toTerm(expr.getOffset()),
                toTerm(expr.getUniquenessIdx().get()));
    }

    private com.microsoft.z3legacy.Expr transformEnumLit(final EnumLitExpr expr) {
        EnumType enumType = expr.getType();
        return ((EnumSort) transformer.toSort(enumType))
                .getConst(enumType.getIntValue(expr.getValue()));
    }

    private com.microsoft.z3legacy.Expr transformEnumEq(final EnumEqExpr expr) {
        final com.microsoft.z3legacy.Expr leftOpTerm = toTerm(expr.getLeftOp());
        final com.microsoft.z3legacy.Expr rightOpTerm = toTerm(expr.getRightOp());
        return context.mkEq(leftOpTerm, rightOpTerm);
    }

    private com.microsoft.z3legacy.Expr transformEnumNeq(final EnumNeqExpr expr) {
        final com.microsoft.z3legacy.Expr leftOpTerm = toTerm(expr.getLeftOp());
        final com.microsoft.z3legacy.Expr rightOpTerm = toTerm(expr.getRightOp());
        return context.mkNot(context.mkEq(leftOpTerm, rightOpTerm));
    }

    public void reset() {
        exprToTerm.invalidateAll();
    }
}
