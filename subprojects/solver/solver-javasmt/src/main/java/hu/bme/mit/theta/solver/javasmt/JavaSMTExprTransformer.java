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
package hu.bme.mit.theta.solver.javasmt;

import static com.google.common.base.Preconditions.checkState;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;
import static hu.bme.mit.theta.core.utils.ExprUtils.extractFuncAndArgs;

import com.google.common.cache.Cache;
import com.google.common.cache.CacheBuilder;
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
import hu.bme.mit.theta.core.type.arraytype.ArrayEqExpr;
import hu.bme.mit.theta.core.type.arraytype.ArrayInitExpr;
import hu.bme.mit.theta.core.type.arraytype.ArrayLitExpr;
import hu.bme.mit.theta.core.type.arraytype.ArrayNeqExpr;
import hu.bme.mit.theta.core.type.arraytype.ArrayReadExpr;
import hu.bme.mit.theta.core.type.arraytype.ArrayWriteExpr;
import hu.bme.mit.theta.core.type.booltype.AndExpr;
import hu.bme.mit.theta.core.type.booltype.ExistsExpr;
import hu.bme.mit.theta.core.type.booltype.FalseExpr;
import hu.bme.mit.theta.core.type.booltype.ForallExpr;
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
import hu.bme.mit.theta.core.type.bvtype.BvSignChangeExpr;
import hu.bme.mit.theta.core.type.bvtype.BvSubExpr;
import hu.bme.mit.theta.core.type.bvtype.BvUDivExpr;
import hu.bme.mit.theta.core.type.bvtype.BvUGeqExpr;
import hu.bme.mit.theta.core.type.bvtype.BvUGtExpr;
import hu.bme.mit.theta.core.type.bvtype.BvULeqExpr;
import hu.bme.mit.theta.core.type.bvtype.BvULtExpr;
import hu.bme.mit.theta.core.type.bvtype.BvURemExpr;
import hu.bme.mit.theta.core.type.bvtype.BvXorExpr;
import hu.bme.mit.theta.core.type.bvtype.BvZExtExpr;
import hu.bme.mit.theta.core.type.enumtype.EnumEqExpr;
import hu.bme.mit.theta.core.type.enumtype.EnumLitExpr;
import hu.bme.mit.theta.core.type.enumtype.EnumNeqExpr;
import hu.bme.mit.theta.core.type.enumtype.EnumType;
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
import hu.bme.mit.theta.core.type.fptype.FpRemExpr;
import hu.bme.mit.theta.core.type.fptype.FpRoundToIntegralExpr;
import hu.bme.mit.theta.core.type.fptype.FpRoundingMode;
import hu.bme.mit.theta.core.type.fptype.FpSqrtExpr;
import hu.bme.mit.theta.core.type.fptype.FpSubExpr;
import hu.bme.mit.theta.core.type.fptype.FpToBvExpr;
import hu.bme.mit.theta.core.type.fptype.FpToFpExpr;
import hu.bme.mit.theta.core.type.functype.FuncAppExpr;
import hu.bme.mit.theta.core.type.functype.FuncType;
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
import hu.bme.mit.theta.core.utils.BvUtils;
import java.util.ArrayList;
import java.util.List;
import java.util.concurrent.ExecutionException;
import java.util.function.Supplier;
import java.util.stream.Collectors;
import java.util.stream.Stream;
import org.sosy_lab.java_smt.api.ArrayFormula;
import org.sosy_lab.java_smt.api.ArrayFormulaManager;
import org.sosy_lab.java_smt.api.BitvectorFormula;
import org.sosy_lab.java_smt.api.BitvectorFormulaManager;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.BooleanFormulaManager;
import org.sosy_lab.java_smt.api.EnumerationFormula;
import org.sosy_lab.java_smt.api.EnumerationFormulaManager;
import org.sosy_lab.java_smt.api.FloatingPointFormula;
import org.sosy_lab.java_smt.api.FloatingPointFormulaManager;
import org.sosy_lab.java_smt.api.FloatingPointRoundingMode;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.FormulaType.FloatingPointType;
import org.sosy_lab.java_smt.api.FunctionDeclaration;
import org.sosy_lab.java_smt.api.IntegerFormulaManager;
import org.sosy_lab.java_smt.api.NumeralFormula;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;
import org.sosy_lab.java_smt.api.NumeralFormula.RationalFormula;
import org.sosy_lab.java_smt.api.QuantifiedFormulaManager;
import org.sosy_lab.java_smt.api.RationalFormulaManager;
import org.sosy_lab.java_smt.api.SolverContext;

final class JavaSMTExprTransformer {

    private static final int CACHE_SIZE = 1000;
    private final BooleanFormulaManager booleanFormulaManager;
    private final IntegerFormulaManager integerFormulaManager;
    private final RationalFormulaManager rationalFormulaManager;
    private final BitvectorFormulaManager bitvectorFormulaManager;
    private final FloatingPointFormulaManager floatingPointFormulaManager;
    private final QuantifiedFormulaManager quantifiedFormulaManager;
    private final ArrayFormulaManager arrayFormulaManager;
    private final EnumerationFormulaManager enumFormulaManager;

    private final JavaSMTTransformationManager transformer;
    private final JavaSMTSymbolTable symbolTable;
    private final SolverContext context;

    private final Cache<Expr<?>, Formula> exprToTerm;
    private final DispatchTable<Formula> table;
    private final Env env;

    public JavaSMTExprTransformer(
            final JavaSMTTransformationManager transformer,
            final JavaSMTSymbolTable symbolTable,
            final SolverContext context) {
        this.symbolTable = symbolTable;
        this.context = context;
        this.transformer = transformer;
        this.env = new Env();

        booleanFormulaManager =
                orElseNull(() -> context.getFormulaManager().getBooleanFormulaManager());
        integerFormulaManager =
                orElseNull(() -> context.getFormulaManager().getIntegerFormulaManager());
        rationalFormulaManager =
                orElseNull(() -> context.getFormulaManager().getRationalFormulaManager());
        bitvectorFormulaManager =
                orElseNull(() -> context.getFormulaManager().getBitvectorFormulaManager());
        floatingPointFormulaManager =
                orElseNull(() -> context.getFormulaManager().getFloatingPointFormulaManager());
        quantifiedFormulaManager =
                orElseNull(() -> context.getFormulaManager().getQuantifiedFormulaManager());
        arrayFormulaManager =
                orElseNull(() -> context.getFormulaManager().getArrayFormulaManager());
        enumFormulaManager =
                orElseNull(() -> context.getFormulaManager().getEnumerationFormulaManager());

        exprToTerm = CacheBuilder.newBuilder().maximumSize(CACHE_SIZE).build();

        table =
                DispatchTable.<Formula>builder()

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
                        .addCase(Dereference.class, this::transformDereference)

                        // Enums

                        .addCase(EnumLitExpr.class, this::transformEnumLit)
                        .addCase(EnumNeqExpr.class, this::transformEnumNeq)
                        .addCase(EnumEqExpr.class, this::transformEnumEq)
                        .build();
    }

    private static <T> T orElseNull(Supplier<T> supplier) {
        try {
            return supplier.get();
        } catch (UnsupportedOperationException uoe) {
            return null;
        }
    }

    private static FloatingPointRoundingMode transformRoundingMode(
            final FpRoundingMode fpRoundingMode) {
        return switch (fpRoundingMode) {
            case RNE -> FloatingPointRoundingMode.NEAREST_TIES_TO_EVEN;
            case RNA -> FloatingPointRoundingMode.NEAREST_TIES_AWAY;
            case RTP -> FloatingPointRoundingMode.TOWARD_POSITIVE;
            case RTN -> FloatingPointRoundingMode.TOWARD_NEGATIVE;
            case RTZ -> FloatingPointRoundingMode.TOWARD_ZERO;
        };
    }

    ////

    /*
     * General
     */

    public Formula toTerm(final Expr<?> expr) {
        try {
            return exprToTerm.get(expr, () -> table.dispatch(expr));
        } catch (final ExecutionException e) {
            throw new AssertionError("Unhandled case: " + expr, e);
        }
    }

    private Formula transformRef(final RefExpr<?> expr) {
        final Decl<?> decl = expr.getDecl();
        if (decl instanceof ConstDecl) {
            return transformer.toSymbol(decl);
        } else if (decl instanceof ParamDecl) {
            return (Formula) env.eval(DeclSymbol.of(decl));
        } else {
            throw new UnsupportedOperationException(
                    "Cannot transform reference for declaration: " + decl);
        }
    }

    /*
     * Booleans
     */

    private Formula transformIte(final IteExpr<?> expr) {
        final BooleanFormula condTerm = (BooleanFormula) toTerm(expr.getCond());
        final Formula thenTerm = toTerm(expr.getThen());
        final Formula elzeTerm = toTerm(expr.getElse());
        return booleanFormulaManager.ifThenElse(condTerm, thenTerm, elzeTerm);
    }

    private Formula transformFalse(final FalseExpr expr) {
        return booleanFormulaManager.makeFalse();
    }

    private Formula transformTrue(final TrueExpr expr) {
        return booleanFormulaManager.makeTrue();
    }

    private Formula transformNot(final NotExpr expr) {
        final BooleanFormula opTerm = (BooleanFormula) toTerm(expr.getOp());
        return booleanFormulaManager.not(opTerm);
    }

    private Formula transformImply(final ImplyExpr expr) {
        final BooleanFormula leftOpTerm = (BooleanFormula) toTerm(expr.getLeftOp());
        final BooleanFormula rightOpTerm = (BooleanFormula) toTerm(expr.getRightOp());
        return booleanFormulaManager.implication(leftOpTerm, rightOpTerm);
    }

    private Formula transformIff(final IffExpr expr) {
        final BooleanFormula leftOpTerm = (BooleanFormula) toTerm(expr.getLeftOp());
        final BooleanFormula rightOpTerm = (BooleanFormula) toTerm(expr.getRightOp());
        return booleanFormulaManager.equivalence(leftOpTerm, rightOpTerm);
    }

    private Formula transformXor(final XorExpr expr) {
        final BooleanFormula leftOpTerm = (BooleanFormula) toTerm(expr.getLeftOp());
        final BooleanFormula rightOpTerm = (BooleanFormula) toTerm(expr.getRightOp());
        return booleanFormulaManager.xor(leftOpTerm, rightOpTerm);
    }

    private Formula transformAnd(final AndExpr expr) {
        final List<BooleanFormula> opTerms =
                expr.getOps().stream().map(e -> (BooleanFormula) toTerm(e)).toList();
        return booleanFormulaManager.and(opTerms);
    }

    private Formula transformOr(final OrExpr expr) {
        final List<BooleanFormula> opTerms =
                expr.getOps().stream().map(e -> (BooleanFormula) toTerm(e)).toList();
        return booleanFormulaManager.or(opTerms);
    }

    private Formula transformExists(final ExistsExpr expr) {
        env.push();
        final List<Formula> paramTerms = transformParamDecls(expr.getParamDecls());
        final BooleanFormula opTerm = (BooleanFormula) toTerm(expr.getOp());
        final BooleanFormula result = quantifiedFormulaManager.exists(paramTerms, opTerm);
        env.pop();
        return result;
    }

    private Formula transformForall(final ForallExpr expr) {
        env.push();
        final List<Formula> paramTerms = transformParamDecls(expr.getParamDecls());
        final BooleanFormula opTerm = (BooleanFormula) toTerm(expr.getOp());
        final BooleanFormula result = quantifiedFormulaManager.forall(paramTerms, opTerm);
        env.pop();
        return result;
    }

    /*
     * Rationals
     */

    private List<Formula> transformParamDecls(final List<ParamDecl<?>> paramDecls) {
        final List<Formula> paramTerms = new ArrayList<>(paramDecls.size());
        for (final ParamDecl<?> paramDecl : paramDecls) {
            final Formula paramSymbol = transformParamDecl(paramDecl);
            paramTerms.add(paramSymbol);
            env.define(DeclSymbol.of(paramDecl), paramSymbol);
        }
        return paramTerms;
    }

    private Formula transformParamDecl(final ParamDecl<?> paramDecl) {
        final Type type = paramDecl.getType();
        if (type instanceof FuncType<?, ?>) {
            throw new UnsupportedOperationException("Only simple types are supported");
        } else {
            final FormulaType<?> sort = transformer.toSort(type);
            return context.getFormulaManager().makeVariable(sort, paramDecl.getName());
        }
    }

    private Formula transformRatLit(final RatLitExpr expr) {
        var num = rationalFormulaManager.makeNumber(expr.getNum().toString());
        var denom = rationalFormulaManager.makeNumber(expr.getDenom().toString());
        return rationalFormulaManager.divide(num, denom);
    }

    private Formula transformRatAdd(final RatAddExpr expr) {
        final List<RationalFormula> opTerms =
                expr.getOps().stream().map(e -> (RationalFormula) toTerm(e)).toList();
        return opTerms.stream().reduce(rationalFormulaManager::add).get();
    }

    private Formula transformRatSub(final RatSubExpr expr) {
        final RationalFormula leftOpTerm = (RationalFormula) toTerm(expr.getLeftOp());
        final RationalFormula rightOpTerm = (RationalFormula) toTerm(expr.getRightOp());
        return rationalFormulaManager.subtract(leftOpTerm, rightOpTerm);
    }

    private Formula transformRatPos(final RatPosExpr expr) {
        return toTerm(expr.getOp());
    }

    private Formula transformRatNeg(final RatNegExpr expr) {
        final RationalFormula opTerm = (RationalFormula) toTerm(expr.getOp());
        return rationalFormulaManager.negate(opTerm);
    }

    private Formula transformRatMul(final RatMulExpr expr) {
        final List<RationalFormula> opTerms =
                expr.getOps().stream().map(e -> (RationalFormula) toTerm(e)).toList();
        return opTerms.stream().reduce(rationalFormulaManager::multiply).get();
    }

    private Formula transformRatDiv(final RatDivExpr expr) {
        final RationalFormula leftOpTerm = (RationalFormula) toTerm(expr.getLeftOp());
        final RationalFormula rightOpTerm = (RationalFormula) toTerm(expr.getRightOp());
        return rationalFormulaManager.divide(leftOpTerm, rightOpTerm);
    }

    private Formula transformRatEq(final RatEqExpr expr) {
        final RationalFormula leftOpTerm = (RationalFormula) toTerm(expr.getLeftOp());
        final RationalFormula rightOpTerm = (RationalFormula) toTerm(expr.getRightOp());
        return rationalFormulaManager.equal(leftOpTerm, rightOpTerm);
    }

    private Formula transformRatNeq(final RatNeqExpr expr) {
        final RationalFormula leftOpTerm = (RationalFormula) toTerm(expr.getLeftOp());
        final RationalFormula rightOpTerm = (RationalFormula) toTerm(expr.getRightOp());
        return booleanFormulaManager.not(rationalFormulaManager.equal(leftOpTerm, rightOpTerm));
    }

    private Formula transformRatGeq(final RatGeqExpr expr) {
        final RationalFormula leftOpTerm = (RationalFormula) toTerm(expr.getLeftOp());
        final RationalFormula rightOpTerm = (RationalFormula) toTerm(expr.getRightOp());
        return rationalFormulaManager.greaterOrEquals(leftOpTerm, rightOpTerm);
    }

    private Formula transformRatGt(final RatGtExpr expr) {
        final RationalFormula leftOpTerm = (RationalFormula) toTerm(expr.getLeftOp());
        final RationalFormula rightOpTerm = (RationalFormula) toTerm(expr.getRightOp());
        return rationalFormulaManager.greaterThan(leftOpTerm, rightOpTerm);
    }

    /*
     * Integers
     */

    private Formula transformRatLeq(final RatLeqExpr expr) {
        final RationalFormula leftOpTerm = (RationalFormula) toTerm(expr.getLeftOp());
        final RationalFormula rightOpTerm = (RationalFormula) toTerm(expr.getRightOp());
        return rationalFormulaManager.lessOrEquals(leftOpTerm, rightOpTerm);
    }

    private Formula transformRatLt(final RatLtExpr expr) {
        final RationalFormula leftOpTerm = (RationalFormula) toTerm(expr.getLeftOp());
        final RationalFormula rightOpTerm = (RationalFormula) toTerm(expr.getRightOp());
        return rationalFormulaManager.lessThan(leftOpTerm, rightOpTerm);
    }

    private Formula transformRatToInt(final RatToIntExpr expr) {
        return rationalFormulaManager.floor((NumeralFormula) toTerm(expr.getOp()));
    }

    private Formula transformIntLit(final IntLitExpr expr) {
        return integerFormulaManager.makeNumber(expr.getValue().toString());
    }

    private Formula transformIntAdd(final IntAddExpr expr) {
        final List<IntegerFormula> opTerms =
                expr.getOps().stream().map(e -> (IntegerFormula) toTerm(e)).toList();
        return opTerms.stream().reduce(integerFormulaManager::add).get();
    }

    private Formula transformIntSub(final IntSubExpr expr) {
        final IntegerFormula leftOpTerm = (IntegerFormula) toTerm(expr.getLeftOp());
        final IntegerFormula rightOpTerm = (IntegerFormula) toTerm(expr.getRightOp());
        return integerFormulaManager.subtract(leftOpTerm, rightOpTerm);
    }

    private Formula transformIntPos(final IntPosExpr expr) {
        return toTerm(expr.getOp());
    }

    private Formula transformIntNeg(final IntNegExpr expr) {
        final IntegerFormula opTerm = (IntegerFormula) toTerm(expr.getOp());
        return integerFormulaManager.negate(opTerm);
    }

    private Formula transformIntMul(final IntMulExpr expr) {
        final List<IntegerFormula> opTerms =
                expr.getOps().stream().map(e -> (IntegerFormula) toTerm(e)).toList();
        return opTerms.stream().reduce(integerFormulaManager::multiply).get();
    }

    private Formula transformIntDiv(final IntDivExpr expr) {
        final IntegerFormula leftOpTerm = (IntegerFormula) toTerm(expr.getLeftOp());
        final IntegerFormula rightOpTerm = (IntegerFormula) toTerm(expr.getRightOp());
        return integerFormulaManager.divide(leftOpTerm, rightOpTerm);
    }

    private Formula transformIntMod(final IntModExpr expr) {
        final IntegerFormula leftOpTerm = (IntegerFormula) toTerm(expr.getLeftOp());
        final IntegerFormula rightOpTerm = (IntegerFormula) toTerm(expr.getRightOp());
        return integerFormulaManager.modulo(leftOpTerm, rightOpTerm);
    }

    private Formula transformIntRem(final IntRemExpr expr) {
        final IntegerFormula leftOpTerm = (IntegerFormula) toTerm(expr.getLeftOp());
        final IntegerFormula rightOpTerm = (IntegerFormula) toTerm(expr.getRightOp());
        return booleanFormulaManager.ifThenElse(
                integerFormulaManager.greaterOrEquals(
                        rightOpTerm, integerFormulaManager.makeNumber(0)),
                integerFormulaManager.modulo(leftOpTerm, rightOpTerm),
                integerFormulaManager.negate(
                        integerFormulaManager.modulo(leftOpTerm, rightOpTerm)));
    }

    private Formula transformIntEq(final IntEqExpr expr) {
        final IntegerFormula leftOpTerm = (IntegerFormula) toTerm(expr.getLeftOp());
        final IntegerFormula rightOpTerm = (IntegerFormula) toTerm(expr.getRightOp());
        return integerFormulaManager.equal(leftOpTerm, rightOpTerm);
    }

    private Formula transformIntNeq(final IntNeqExpr expr) {
        final IntegerFormula leftOpTerm = (IntegerFormula) toTerm(expr.getLeftOp());
        final IntegerFormula rightOpTerm = (IntegerFormula) toTerm(expr.getRightOp());
        return booleanFormulaManager.not(integerFormulaManager.equal(leftOpTerm, rightOpTerm));
    }

    private Formula transformIntGeq(final IntGeqExpr expr) {
        final IntegerFormula leftOpTerm = (IntegerFormula) toTerm(expr.getLeftOp());
        final IntegerFormula rightOpTerm = (IntegerFormula) toTerm(expr.getRightOp());
        return integerFormulaManager.greaterOrEquals(leftOpTerm, rightOpTerm);
    }

    private Formula transformIntGt(final IntGtExpr expr) {
        final IntegerFormula leftOpTerm = (IntegerFormula) toTerm(expr.getLeftOp());
        final IntegerFormula rightOpTerm = (IntegerFormula) toTerm(expr.getRightOp());
        return integerFormulaManager.greaterThan(leftOpTerm, rightOpTerm);
    }

    private Formula transformIntLeq(final IntLeqExpr expr) {
        final IntegerFormula leftOpTerm = (IntegerFormula) toTerm(expr.getLeftOp());
        final IntegerFormula rightOpTerm = (IntegerFormula) toTerm(expr.getRightOp());
        return integerFormulaManager.lessOrEquals(leftOpTerm, rightOpTerm);
    }

    /*
     * Bitvectors
     */

    private Formula transformIntLt(final IntLtExpr expr) {
        final IntegerFormula leftOpTerm = (IntegerFormula) toTerm(expr.getLeftOp());
        final IntegerFormula rightOpTerm = (IntegerFormula) toTerm(expr.getRightOp());
        return integerFormulaManager.lessThan(leftOpTerm, rightOpTerm);
    }

    private Formula transformIntToRat(final IntToRatExpr expr) {
        return rationalFormulaManager.sum(List.of((IntegerFormula) toTerm(expr.getOp())));
    }

    private Formula transformBvLit(final BvLitExpr expr) {
        return bitvectorFormulaManager.makeBitvector(
                expr.getType().getSize(), BvUtils.neutralBvLitExprToBigInteger(expr));
    }

    private Formula transformBvEq(final BvEqExpr expr) {
        final BitvectorFormula leftOpTerm = (BitvectorFormula) toTerm(expr.getLeftOp());
        final BitvectorFormula rightOpTerm = (BitvectorFormula) toTerm(expr.getRightOp());
        return bitvectorFormulaManager.equal(leftOpTerm, rightOpTerm);
    }

    private Formula transformBvNeq(final BvNeqExpr expr) {
        final BitvectorFormula leftOpTerm = (BitvectorFormula) toTerm(expr.getLeftOp());
        final BitvectorFormula rightOpTerm = (BitvectorFormula) toTerm(expr.getRightOp());
        return booleanFormulaManager.not(bitvectorFormulaManager.equal(leftOpTerm, rightOpTerm));
    }

    private Formula transformBvConcat(final BvConcatExpr expr) {
        final BitvectorFormula[] opTerms =
                expr.getOps().stream()
                        .map(e -> (BitvectorFormula) toTerm(e))
                        .toArray(BitvectorFormula[]::new);

        return Stream.of(opTerms).skip(1).reduce(opTerms[0], bitvectorFormulaManager::concat);
    }

    private Formula transformBvExtract(final BvExtractExpr expr) {
        final BitvectorFormula bitvecTerm = (BitvectorFormula) toTerm(expr.getBitvec());
        final int from = expr.getFrom().getValue().intValue();
        final int until = expr.getUntil().getValue().intValue();

        return bitvectorFormulaManager.extract(bitvecTerm, until - 1, from);
    }

    private Formula transformBvZExt(final BvZExtExpr expr) {
        final BitvectorFormula bitvecTerm = (BitvectorFormula) toTerm(expr.getOp());
        final int extendWith = expr.getExtendType().getSize() - expr.getOp().getType().getSize();

        return bitvectorFormulaManager.extend(bitvecTerm, extendWith, false);
    }

    private Formula transformBvSExt(final BvSExtExpr expr) {
        final BitvectorFormula bitvecTerm = (BitvectorFormula) toTerm(expr.getOp());
        final int extendWith = expr.getExtendType().getSize() - expr.getOp().getType().getSize();

        return bitvectorFormulaManager.extend(bitvecTerm, extendWith, true);
    }

    private Formula transformBvAdd(final BvAddExpr expr) {
        final BitvectorFormula[] opTerms =
                expr.getOps().stream()
                        .map(e -> (BitvectorFormula) toTerm(e))
                        .toArray(BitvectorFormula[]::new);

        return Stream.of(opTerms).skip(1).reduce(opTerms[0], bitvectorFormulaManager::add);
    }

    private Formula transformBvSub(final BvSubExpr expr) {
        final BitvectorFormula leftOpTerm = (BitvectorFormula) toTerm(expr.getLeftOp());
        final BitvectorFormula rightOpTerm = (BitvectorFormula) toTerm(expr.getRightOp());
        return bitvectorFormulaManager.subtract(leftOpTerm, rightOpTerm);
    }

    private Formula transformBvPos(final BvPosExpr expr) {
        return toTerm(expr.getOp());
    }

    private Formula transformBvSignChange(final BvSignChangeExpr expr) {
        return (BitvectorFormula) toTerm(expr.getOp());
    }

    private Formula transformBvNeg(final BvNegExpr expr) {
        final BitvectorFormula opTerm = (BitvectorFormula) toTerm(expr.getOp());
        return bitvectorFormulaManager.negate(opTerm);
    }

    private Formula transformBvMul(final BvMulExpr expr) {
        final BitvectorFormula[] opTerms =
                expr.getOps().stream()
                        .map(e -> (BitvectorFormula) toTerm(e))
                        .toArray(BitvectorFormula[]::new);

        return Stream.of(opTerms).skip(1).reduce(opTerms[0], bitvectorFormulaManager::multiply);
    }

    private Formula transformBvUDiv(final BvUDivExpr expr) {
        final BitvectorFormula leftOpTerm = (BitvectorFormula) toTerm(expr.getLeftOp());
        final BitvectorFormula rightOpTerm = (BitvectorFormula) toTerm(expr.getRightOp());

        return bitvectorFormulaManager.divide(leftOpTerm, rightOpTerm, false);
    }

    private Formula transformBvSDiv(final BvSDivExpr expr) {
        final BitvectorFormula leftOpTerm = (BitvectorFormula) toTerm(expr.getLeftOp());
        final BitvectorFormula rightOpTerm = (BitvectorFormula) toTerm(expr.getRightOp());

        return bitvectorFormulaManager.divide(leftOpTerm, rightOpTerm, true);
    }

    private Formula transformBvSMod(final BvSModExpr expr) {
        final BitvectorFormula leftOpTerm = (BitvectorFormula) toTerm(expr.getLeftOp());
        final BitvectorFormula rightOpTerm = (BitvectorFormula) toTerm(expr.getRightOp());

        return bitvectorFormulaManager.smodulo(leftOpTerm, rightOpTerm);
    }

    private Formula transformBvURem(final BvURemExpr expr) {
        final BitvectorFormula leftOpTerm = (BitvectorFormula) toTerm(expr.getLeftOp());
        final BitvectorFormula rightOpTerm = (BitvectorFormula) toTerm(expr.getRightOp());

        return bitvectorFormulaManager.remainder(leftOpTerm, rightOpTerm, false);
    }

    private Formula transformBvSRem(final BvSRemExpr expr) {
        final BitvectorFormula leftOpTerm = (BitvectorFormula) toTerm(expr.getLeftOp());
        final BitvectorFormula rightOpTerm = (BitvectorFormula) toTerm(expr.getRightOp());

        return bitvectorFormulaManager.remainder(leftOpTerm, rightOpTerm, true);
    }

    private Formula transformBvAnd(final BvAndExpr expr) {
        final BitvectorFormula[] opTerms =
                expr.getOps().stream()
                        .map(e -> (BitvectorFormula) toTerm(e))
                        .toArray(BitvectorFormula[]::new);

        return Stream.of(opTerms).skip(1).reduce(opTerms[0], bitvectorFormulaManager::and);
    }

    private Formula transformBvOr(final BvOrExpr expr) {
        final BitvectorFormula[] opTerms =
                expr.getOps().stream()
                        .map(e -> (BitvectorFormula) toTerm(e))
                        .toArray(BitvectorFormula[]::new);

        return Stream.of(opTerms).skip(1).reduce(opTerms[0], bitvectorFormulaManager::or);
    }

    private Formula transformBvXor(final BvXorExpr expr) {
        final BitvectorFormula[] opTerms =
                expr.getOps().stream()
                        .map(e -> (BitvectorFormula) toTerm(e))
                        .toArray(BitvectorFormula[]::new);

        return Stream.of(opTerms).skip(1).reduce(opTerms[0], bitvectorFormulaManager::xor);
    }

    private Formula transformBvNot(final BvNotExpr expr) {
        final BitvectorFormula opTerm = (BitvectorFormula) toTerm(expr.getOp());

        return bitvectorFormulaManager.not(opTerm);
    }

    private Formula transformBvShiftLeft(final BvShiftLeftExpr expr) {
        final BitvectorFormula leftOpTerm = (BitvectorFormula) toTerm(expr.getLeftOp());
        final BitvectorFormula rightOpTerm = (BitvectorFormula) toTerm(expr.getRightOp());

        return bitvectorFormulaManager.shiftLeft(leftOpTerm, rightOpTerm);
    }

    private Formula transformBvArithShiftRight(final BvArithShiftRightExpr expr) {
        final BitvectorFormula leftOpTerm = (BitvectorFormula) toTerm(expr.getLeftOp());
        final BitvectorFormula rightOpTerm = (BitvectorFormula) toTerm(expr.getRightOp());

        return bitvectorFormulaManager.shiftRight(leftOpTerm, rightOpTerm, true);
    }

    private Formula transformBvLogicShiftRight(final BvLogicShiftRightExpr expr) {
        final BitvectorFormula leftOpTerm = (BitvectorFormula) toTerm(expr.getLeftOp());
        final BitvectorFormula rightOpTerm = (BitvectorFormula) toTerm(expr.getRightOp());

        return bitvectorFormulaManager.shiftRight(leftOpTerm, rightOpTerm, false);
    }

    private Formula transformBvRotateLeft(final BvRotateLeftExpr expr) {
        final BitvectorFormula leftOpTerm = (BitvectorFormula) toTerm(expr.getLeftOp());
        final BitvectorFormula rightOpTerm = (BitvectorFormula) toTerm(expr.getRightOp());

        return bitvectorFormulaManager.rotateLeft(leftOpTerm, rightOpTerm);
    }

    private Formula transformBvRotateRight(final BvRotateRightExpr expr) {
        final BitvectorFormula leftOpTerm = (BitvectorFormula) toTerm(expr.getLeftOp());
        final BitvectorFormula rightOpTerm = (BitvectorFormula) toTerm(expr.getRightOp());

        return bitvectorFormulaManager.rotateRight(leftOpTerm, rightOpTerm);
    }

    private Formula transformBvUGeq(final BvUGeqExpr expr) {
        final BitvectorFormula leftOpTerm = (BitvectorFormula) toTerm(expr.getLeftOp());
        final BitvectorFormula rightOpTerm = (BitvectorFormula) toTerm(expr.getRightOp());

        return bitvectorFormulaManager.greaterOrEquals(leftOpTerm, rightOpTerm, false);
    }

    private Formula transformBvUGt(final BvUGtExpr expr) {
        final BitvectorFormula leftOpTerm = (BitvectorFormula) toTerm(expr.getLeftOp());
        final BitvectorFormula rightOpTerm = (BitvectorFormula) toTerm(expr.getRightOp());

        return bitvectorFormulaManager.greaterThan(leftOpTerm, rightOpTerm, false);
    }

    private Formula transformBvULeq(final BvULeqExpr expr) {
        final BitvectorFormula leftOpTerm = (BitvectorFormula) toTerm(expr.getLeftOp());
        final BitvectorFormula rightOpTerm = (BitvectorFormula) toTerm(expr.getRightOp());

        return bitvectorFormulaManager.lessOrEquals(leftOpTerm, rightOpTerm, false);
    }

    private Formula transformBvULt(final BvULtExpr expr) {
        final BitvectorFormula leftOpTerm = (BitvectorFormula) toTerm(expr.getLeftOp());
        final BitvectorFormula rightOpTerm = (BitvectorFormula) toTerm(expr.getRightOp());

        return bitvectorFormulaManager.lessThan(leftOpTerm, rightOpTerm, false);
    }

    private Formula transformBvSGeq(final BvSGeqExpr expr) {
        final BitvectorFormula leftOpTerm = (BitvectorFormula) toTerm(expr.getLeftOp());
        final BitvectorFormula rightOpTerm = (BitvectorFormula) toTerm(expr.getRightOp());

        return bitvectorFormulaManager.greaterOrEquals(leftOpTerm, rightOpTerm, true);
    }

    private Formula transformBvSGt(final BvSGtExpr expr) {
        final BitvectorFormula leftOpTerm = (BitvectorFormula) toTerm(expr.getLeftOp());
        final BitvectorFormula rightOpTerm = (BitvectorFormula) toTerm(expr.getRightOp());

        return bitvectorFormulaManager.greaterThan(leftOpTerm, rightOpTerm, true);
    }

    /*
     * Floating points
     */

    private Formula transformBvSLeq(final BvSLeqExpr expr) {
        final BitvectorFormula leftOpTerm = (BitvectorFormula) toTerm(expr.getLeftOp());
        final BitvectorFormula rightOpTerm = (BitvectorFormula) toTerm(expr.getRightOp());

        return bitvectorFormulaManager.lessOrEquals(leftOpTerm, rightOpTerm, true);
    }

    private Formula transformBvSLt(final BvSLtExpr expr) {
        final BitvectorFormula leftOpTerm = (BitvectorFormula) toTerm(expr.getLeftOp());
        final BitvectorFormula rightOpTerm = (BitvectorFormula) toTerm(expr.getRightOp());

        return bitvectorFormulaManager.lessThan(leftOpTerm, rightOpTerm, true);
    }

    private Formula transformFpLit(final FpLitExpr expr) {
        return floatingPointFormulaManager.makeNumber(
                BvUtils.neutralBvLitExprToBigInteger(expr.getExponent()),
                BvUtils.neutralBvLitExprToBigInteger(expr.getSignificand()),
                expr.getHidden(),
                FloatingPointType.getFloatingPointType(
                        expr.getType().getExponent(), expr.getType().getSignificand() - 1));
    }

    private Formula transformFpAdd(final FpAddExpr expr) {
        final FloatingPointFormula[] opTerms =
                expr.getOps().stream()
                        .map(e -> (FloatingPointFormula) toTerm(e))
                        .toArray(FloatingPointFormula[]::new);

        return Stream.of(opTerms)
                .skip(1)
                .reduce(
                        opTerms[0],
                        (op1, op2) ->
                                floatingPointFormulaManager.add(
                                        op1, op2, transformFpRoundingMode(expr.getRoundingMode())));
    }

    private Formula transformFpSub(final FpSubExpr expr) {
        final FloatingPointFormula leftOpTerm = (FloatingPointFormula) toTerm(expr.getLeftOp());
        final FloatingPointFormula rightOpTerm = (FloatingPointFormula) toTerm(expr.getRightOp());
        return floatingPointFormulaManager.subtract(
                leftOpTerm, rightOpTerm, transformFpRoundingMode(expr.getRoundingMode()));
    }

    private Formula transformFpPos(final FpPosExpr expr) {
        return toTerm(expr.getOp());
    }

    private Formula transformFpNeg(final FpNegExpr expr) {
        final FloatingPointFormula opTerm = (FloatingPointFormula) toTerm(expr.getOp());
        return floatingPointFormulaManager.negate(opTerm);
    }

    private Formula transformFpAbs(final FpAbsExpr expr) {
        final FloatingPointFormula opTerm = (FloatingPointFormula) toTerm(expr.getOp());
        return floatingPointFormulaManager.abs(opTerm);
    }

    private Formula transformFpIsNan(final FpIsNanExpr expr) {
        final FloatingPointFormula opTerm = (FloatingPointFormula) toTerm(expr.getOp());
        return floatingPointFormulaManager.isNaN(opTerm);
    }

    private Formula transformFpIsInfinite(final FpIsInfiniteExpr expr) {
        final FloatingPointFormula opTerm = (FloatingPointFormula) toTerm(expr.getOp());
        return floatingPointFormulaManager.isInfinity(opTerm);
    }

    private Formula transformFpSqrt(final FpSqrtExpr expr) {
        final FloatingPointFormula opTerm = (FloatingPointFormula) toTerm(expr.getOp());
        return floatingPointFormulaManager.sqrt(
                opTerm, transformFpRoundingMode(expr.getRoundingMode()));
    }

    private Formula transformFpRoundToIntegral(final FpRoundToIntegralExpr expr) {
        final FloatingPointFormula opTerm = (FloatingPointFormula) toTerm(expr.getOp());
        return floatingPointFormulaManager.round(
                opTerm, transformFpRoundingMode(expr.getRoundingMode()));
    }

    private Formula transformFpMul(final FpMulExpr expr) {
        final FloatingPointFormula[] opTerms =
                expr.getOps().stream()
                        .map(e -> (FloatingPointFormula) toTerm(e))
                        .toArray(FloatingPointFormula[]::new);

        return Stream.of(opTerms)
                .skip(1)
                .reduce(
                        opTerms[0],
                        (op1, op2) ->
                                floatingPointFormulaManager.multiply(
                                        op1, op2, transformFpRoundingMode(expr.getRoundingMode())));
    }

    private Formula transformFpDiv(final FpDivExpr expr) {
        final FloatingPointFormula leftOpTerm = (FloatingPointFormula) toTerm(expr.getLeftOp());
        final FloatingPointFormula rightOpTerm = (FloatingPointFormula) toTerm(expr.getRightOp());

        return floatingPointFormulaManager.divide(
                leftOpTerm, rightOpTerm, transformFpRoundingMode(expr.getRoundingMode()));
    }

    private Formula transformFpRem(final FpRemExpr expr) {
        final FloatingPointFormula leftOpTerm = (FloatingPointFormula) toTerm(expr.getLeftOp());
        final FloatingPointFormula rightOpTerm = (FloatingPointFormula) toTerm(expr.getRightOp());
        return floatingPointFormulaManager.remainder(leftOpTerm, rightOpTerm);
    }

    private Formula transformFpEq(final FpEqExpr expr) {
        final Formula leftOpTerm = toTerm(expr.getLeftOp());
        final Formula rightOpTerm = toTerm(expr.getRightOp());
        return floatingPointFormulaManager.equalWithFPSemantics(
                (FloatingPointFormula) leftOpTerm, (FloatingPointFormula) rightOpTerm);
    }

    private Formula transformFpAssign(final FpAssignExpr expr) {
        final Formula leftOpTerm = toTerm(expr.getLeftOp());
        final Formula rightOpTerm = toTerm(expr.getRightOp());
        return floatingPointFormulaManager.assignment(
                (FloatingPointFormula) leftOpTerm, (FloatingPointFormula) rightOpTerm);
    }

    private Formula transformFpNeq(final FpNeqExpr expr) {
        final Formula leftOpTerm = toTerm(expr.getLeftOp());
        final Formula rightOpTerm = toTerm(expr.getRightOp());
        return booleanFormulaManager.not(
                floatingPointFormulaManager.equalWithFPSemantics(
                        (FloatingPointFormula) leftOpTerm, (FloatingPointFormula) rightOpTerm));
    }

    private Formula transformFpGeq(final FpGeqExpr expr) {
        final Formula leftOpTerm = toTerm(expr.getLeftOp());
        final Formula rightOpTerm = toTerm(expr.getRightOp());
        return floatingPointFormulaManager.greaterOrEquals(
                (FloatingPointFormula) leftOpTerm, (FloatingPointFormula) rightOpTerm);
    }

    private Formula transformFpLeq(final FpLeqExpr expr) {
        final Formula leftOpTerm = toTerm(expr.getLeftOp());
        final Formula rightOpTerm = toTerm(expr.getRightOp());
        return floatingPointFormulaManager.lessOrEquals(
                (FloatingPointFormula) leftOpTerm, (FloatingPointFormula) rightOpTerm);
    }

    private Formula transformFpGt(final FpGtExpr expr) {
        final Formula leftOpTerm = toTerm(expr.getLeftOp());
        final Formula rightOpTerm = toTerm(expr.getRightOp());
        return floatingPointFormulaManager.greaterThan(
                (FloatingPointFormula) leftOpTerm, (FloatingPointFormula) rightOpTerm);
    }

    private Formula transformFpLt(final FpLtExpr expr) {
        final Formula leftOpTerm = toTerm(expr.getLeftOp());
        final Formula rightOpTerm = toTerm(expr.getRightOp());
        return floatingPointFormulaManager.lessThan(
                (FloatingPointFormula) leftOpTerm, (FloatingPointFormula) rightOpTerm);
    }

    private FloatingPointRoundingMode transformFpRoundingMode(final FpRoundingMode roundingMode) {
        return switch (roundingMode) {
            case RNE -> FloatingPointRoundingMode.NEAREST_TIES_TO_EVEN;
            case RNA -> FloatingPointRoundingMode.NEAREST_TIES_AWAY;
            case RTP -> FloatingPointRoundingMode.TOWARD_POSITIVE;
            case RTN -> FloatingPointRoundingMode.TOWARD_NEGATIVE;
            case RTZ -> FloatingPointRoundingMode.TOWARD_ZERO;
        };
    }

    private Formula transformFpMax(final FpMaxExpr expr) {
        final FloatingPointFormula leftOpTerm = (FloatingPointFormula) toTerm(expr.getLeftOp());
        final FloatingPointFormula rightOpTerm = (FloatingPointFormula) toTerm(expr.getRightOp());
        return floatingPointFormulaManager.max(leftOpTerm, rightOpTerm);
    }

    private Formula transformFpMin(final FpMinExpr expr) {
        final FloatingPointFormula leftOpTerm = (FloatingPointFormula) toTerm(expr.getLeftOp());
        final FloatingPointFormula rightOpTerm = (FloatingPointFormula) toTerm(expr.getRightOp());
        return floatingPointFormulaManager.min(leftOpTerm, rightOpTerm);
    }

    private Formula transformFpFromBv(final FpFromBvExpr expr) {
        final BitvectorFormula val = (BitvectorFormula) toTerm(expr.getOp());
        final FloatingPointType fpSort =
                FloatingPointType.getFloatingPointType(
                        expr.getFpType().getExponent(), expr.getFpType().getSignificand() - 1);
        return floatingPointFormulaManager.castFrom(val, expr.isSigned(), fpSort);
    }

    /*
     * Arrays
     */

    private Formula transformFpToBv(final FpToBvExpr expr) {
        final FloatingPointFormula op = (FloatingPointFormula) toTerm(expr.getOp());
        final FloatingPointRoundingMode roundingMode =
                transformRoundingMode(expr.getRoundingMode());

        return floatingPointFormulaManager.castTo(
                op,
                expr.getSgn(),
                FormulaType.getBitvectorTypeWithSize(expr.getSize()),
                roundingMode);
    }

    private Formula transformFpToFp(final FpToFpExpr expr) {
        final FloatingPointFormula op = (FloatingPointFormula) toTerm(expr.getOp());

        return floatingPointFormulaManager.castTo(
                op,
                true, // ignored
                FloatingPointType.getFloatingPointType(expr.getExpBits(), expr.getSignBits() - 1),
                transformFpRoundingMode(expr.getRoundingMode()));
    }

    private Formula transformArrayRead(final ArrayReadExpr<?, ?> expr) {
        final ArrayFormula arrayTerm = (ArrayFormula) toTerm(expr.getArray());
        final Formula indexTerm = toTerm(expr.getIndex());
        return arrayFormulaManager.select(arrayTerm, indexTerm);
    }

    private Formula transformArrayWrite(final ArrayWriteExpr<?, ?> expr) {
        final ArrayFormula arrayTerm = (ArrayFormula) toTerm(expr.getArray());
        final Formula indexTerm = toTerm(expr.getIndex());
        final Formula elemTerm = toTerm(expr.getElem());
        return arrayFormulaManager.store(arrayTerm, indexTerm, elemTerm);
    }

    private <T1 extends Formula, T2 extends Formula> Formula transformArrayEq(
            final ArrayEqExpr<?, ?> expr) {
        final ArrayFormula<T1, T2> leftOpTerm = (ArrayFormula<T1, T2>) toTerm(expr.getLeftOp());
        final ArrayFormula<T1, T2> rightOpTerm = (ArrayFormula<T1, T2>) toTerm(expr.getRightOp());
        return arrayFormulaManager.equivalence(leftOpTerm, rightOpTerm);
    }

    private Formula transformArrayNeq(final ArrayNeqExpr<?, ?> expr) {
        return booleanFormulaManager.not(
                (BooleanFormula)
                        transformArrayEq(ArrayEqExpr.create(expr.getLeftOp(), expr.getRightOp())));
    }

    private <TI extends Formula, TE extends Formula> Formula transformArrayLit(
            final ArrayLitExpr<?, ?> expr) {
        throw new UnsupportedOperationException();
        //        final TE elseElem = (TE) toTerm(expr.getElseElem());
        //        final FormulaType<TE> elemType =
        //                (FormulaType<TE>) transformer.toSort(expr.getType().getElemType());
        //        final FormulaType<TI> indexType =
        //                (FormulaType<TI>) transformer.toSort(expr.getType().getIndexType());
        //        var arr = arrayFormulaManager.makeArray(elseElem, indexType, elemType);
        //        for (Tuple2<? extends LitExpr<?>, ? extends LitExpr<?>> element :
        // expr.getElements()) {
        //            final TI index = (TI) toTerm(element.get1());
        //            final TE elem = (TE) toTerm(element.get2());
        //            arr = arrayFormulaManager.store(arr, index, elem);
        //        }
        //        return arr;
    }

    /*
     * Functions
     */

    private <TI extends Formula, TE extends Formula> Formula transformArrayInit(
            final ArrayInitExpr<?, ?> expr) {
        throw new UnsupportedOperationException();
        //        final TE elseElem = (TE) toTerm(expr.getElseElem());
        //        final FormulaType<TE> elemType =
        //                (FormulaType<TE>) transformer.toSort(expr.getType().getElemType());
        //        final FormulaType<TI> indexType =
        //                (FormulaType<TI>) transformer.toSort(expr.getType().getIndexType());
        //        var arr = arrayFormulaManager.makeArray(elseElem, indexType, elemType);
        //        for (Tuple2<? extends Expr<?>, ? extends Expr<?>> element : expr.getElements()) {
        //            final TI index = (TI) toTerm(element.get1());
        //            final TE elem = (TE) toTerm(element.get2());
        //            arr = arrayFormulaManager.store(arr, index, elem);
        //        }
        //        return arr;
    }

    private Formula transformFuncApp(final FuncAppExpr<?, ?> expr) {
        final Tuple2<Expr<?>, List<Expr<?>>> funcAndArgs = extractFuncAndArgs(expr);
        final Expr<?> func = funcAndArgs.get1();
        if (func instanceof RefExpr) {
            final RefExpr<?> ref = (RefExpr<?>) func;
            final ConstDecl<?> decl = (ConstDecl<?>) ref.getDecl();
            final String name = decl.getName();

            final List<Expr<?>> args = funcAndArgs.get2();
            final List<Formula> argTerms = args.stream().map(this::toTerm).toList();

            final FunctionDeclaration<?> funcDecl;
            if (symbolTable.definesConstAsFunction(decl)) {
                funcDecl = symbolTable.getSymbolAsFunction(decl);
            } else {
                funcDecl =
                        context.getFormulaManager()
                                .getUFManager()
                                .declareUF(
                                        name,
                                        transformer.toSort(expr.getType()),
                                        argTerms.stream()
                                                .map(context.getFormulaManager()::getFormulaType)
                                                .collect(Collectors.toList()));

                symbolTable.put(decl, funcDecl);
            }

            return context.getFormulaManager().getUFManager().callUF(funcDecl, argTerms);
        } else {
            throw new UnsupportedOperationException(
                    "Higher order functions are not supported: " + func);
        }
    }

    private Formula transformDereference(final Dereference<?, ?, ?> expr) {
        checkState(
                expr.getUniquenessIdx().isPresent(),
                "Incomplete dereferences (missing uniquenessIdx) are not handled properly.");
        final var sort = transformer.toSort(expr.getArray().getType());
        final var sortName = expr.getArray().getType().toString() + "-" + expr.getType().toString();
        final var constSort = transformer.toSort(Int());
        final var funcDecl =
                context.getFormulaManager()
                        .getUFManager()
                        .declareUF(
                                "deref-" + sortName.replaceAll(" ", "_"),
                                transformer.toSort(expr.getType()),
                                List.of(sort, sort, constSort));

        final var func =
                context.getFormulaManager()
                        .getUFManager()
                        .callUF(
                                funcDecl,
                                toTerm(expr.getArray()),
                                toTerm(expr.getOffset()),
                                toTerm(expr.getUniquenessIdx().get()));
        return func;
    }

    // Enums

    private Formula transformEnumEq(EnumEqExpr enumEqExpr) {
        return enumFormulaManager.equivalence(
                (EnumerationFormula) toTerm(enumEqExpr.getLeftOp()),
                (EnumerationFormula) toTerm(enumEqExpr.getRightOp()));
    }

    private Formula transformEnumLit(EnumLitExpr enumLitExpr) {
        return enumFormulaManager.makeConstant(
                EnumType.makeLongName(enumLitExpr.getType(), enumLitExpr.getValue()),
                (FormulaType.EnumerationFormulaType) transformer.toSort(enumLitExpr.getType()));
    }

    private Formula transformEnumNeq(EnumNeqExpr enumNeqExpr) {
        return booleanFormulaManager.not(
                enumFormulaManager.equivalence(
                        (EnumerationFormula) toTerm(enumNeqExpr.getLeftOp()),
                        (EnumerationFormula) toTerm(enumNeqExpr.getRightOp())));
    }

    public void reset() {
        exprToTerm.invalidateAll();
    }
}
