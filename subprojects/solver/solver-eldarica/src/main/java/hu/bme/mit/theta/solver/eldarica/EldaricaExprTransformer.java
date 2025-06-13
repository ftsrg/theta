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
package hu.bme.mit.theta.solver.eldarica;

import static ap.parser.IExpression.*;
import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Geq;
import static hu.bme.mit.theta.core.type.anytype.Exprs.Ite;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.*;
import static hu.bme.mit.theta.core.utils.ExprUtils.extractFuncAndArgs;
import static hu.bme.mit.theta.solver.eldarica.Utils.PredTermFormula.wrap;
import static hu.bme.mit.theta.solver.eldarica.Utils.getIterable;
import static hu.bme.mit.theta.solver.eldarica.Utils.toSeq;

import ap.basetypes.IdealInt;
import ap.parser.*;
import ap.terfor.preds.Predicate;
import ap.theories.arrays.ExtArray;
import ap.theories.bitvectors.ModuloArithmetic$;
import ap.types.Sort$;
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
import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.core.type.anytype.IteExpr;
import hu.bme.mit.theta.core.type.anytype.RefExpr;
import hu.bme.mit.theta.core.type.arraytype.*;
import hu.bme.mit.theta.core.type.booltype.*;
import hu.bme.mit.theta.core.type.bvtype.*;
import hu.bme.mit.theta.core.type.functype.FuncAppExpr;
import hu.bme.mit.theta.core.type.inttype.*;
import hu.bme.mit.theta.core.utils.BvUtils;
import java.math.BigInteger;
import java.util.List;
import java.util.concurrent.ExecutionException;
import scala.collection.immutable.Seq;

final class EldaricaExprTransformer {

    private static final int CACHE_SIZE = 1000;

    private final Cache<Expr<?>, Utils.PredTermFormula> exprToTerm;
    private final DispatchTable<Utils.PredTermFormula> table;
    private final Env env;
    private final EldaricaTransformationManager transformer;

    public EldaricaExprTransformer(final EldaricaTransformationManager transformer) {
        this.transformer = transformer;
        this.env = new Env();

        exprToTerm = CacheBuilder.newBuilder().maximumSize(CACHE_SIZE).build();

        table =
                DispatchTable.<Utils.PredTermFormula>builder()

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
                        //
                        //                        // Rationals
                        //
                        //                        .addCase(RatLitExpr.class, this::transformRatLit)
                        //                        .addCase(RatAddExpr.class, this::transformRatAdd)
                        //                        .addCase(RatSubExpr.class, this::transformRatSub)
                        //                        .addCase(RatPosExpr.class, this::transformRatPos)
                        //                        .addCase(RatNegExpr.class, this::transformRatNeg)
                        //                        .addCase(RatMulExpr.class, this::transformRatMul)
                        //                        .addCase(RatDivExpr.class, this::transformRatDiv)
                        //                        .addCase(RatEqExpr.class, this::transformRatEq)
                        //                        .addCase(RatNeqExpr.class, this::transformRatNeq)
                        //                        .addCase(RatGeqExpr.class, this::transformRatGeq)
                        //                        .addCase(RatGtExpr.class, this::transformRatGt)
                        //                        .addCase(RatLeqExpr.class, this::transformRatLeq)
                        //                        .addCase(RatLtExpr.class, this::transformRatLt)
                        //                        .addCase(RatToIntExpr.class,
                        // this::transformRatToInt)
                        //
                        //                        // Integers
                        //
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
                        //                        .addCase(IntToRatExpr.class,
                        // this::transformIntToRat)
                        //
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
                        //
                        //                        // Floating points
                        //
                        //                        .addCase(FpLitExpr.class, this::transformFpLit)
                        //                        .addCase(FpAddExpr.class, this::transformFpAdd)
                        //                        .addCase(FpSubExpr.class, this::transformFpSub)
                        //                        .addCase(FpPosExpr.class, this::transformFpPos)
                        //                        .addCase(FpNegExpr.class, this::transformFpNeg)
                        //                        .addCase(FpMulExpr.class, this::transformFpMul)
                        //                        .addCase(FpDivExpr.class, this::transformFpDiv)
                        //                        .addCase(FpEqExpr.class, this::transformFpEq)
                        //                        .addCase(FpAssignExpr.class,
                        // this::transformFpAssign)
                        //                        .addCase(FpGeqExpr.class, this::transformFpGeq)
                        //                        .addCase(FpLeqExpr.class, this::transformFpLeq)
                        //                        .addCase(FpGtExpr.class, this::transformFpGt)
                        //                        .addCase(FpLtExpr.class, this::transformFpLt)
                        //                        .addCase(FpNeqExpr.class, this::transformFpNeq)
                        //                        .addCase(FpAbsExpr.class, this::transformFpAbs)
                        //                        .addCase(FpRoundToIntegralExpr.class,
                        // this::transformFpRoundToIntegral)
                        //                        .addCase(FpMaxExpr.class, this::transformFpMax)
                        //                        .addCase(FpMinExpr.class, this::transformFpMin)
                        //                        .addCase(FpSqrtExpr.class, this::transformFpSqrt)
                        //                        .addCase(FpRemExpr.class, this::transformFpRem)
                        //                        .addCase(FpIsNanExpr.class,
                        // this::transformFpIsNan)
                        //                        .addCase(FpIsInfiniteExpr.class,
                        // this::transformFpIsInfinite)
                        //                        .addCase(FpFromBvExpr.class,
                        // this::transformFpFromBv)
                        //                        .addCase(FpToBvExpr.class, this::transformFpToBv)
                        //                        .addCase(FpToFpExpr.class, this::transformFpToFp)
                        //
                        //                        // Functions
                        //
                        .addCase(FuncAppExpr.class, this::transformFuncApp)
                        //
                        //                        // Arrays

                        .addCase(ArrayReadExpr.class, this::transformArrayRead)
                        .addCase(ArrayWriteExpr.class, this::transformArrayWrite)
                        .addCase(ArrayEqExpr.class, this::transformArrayEq)
                        .addCase(ArrayNeqExpr.class, this::transformArrayNeq)
                        .addCase(ArrayLitExpr.class, this::transformArrayLit)
                        .addCase(ArrayInitExpr.class, this::transformArrayInit)

                        //                        // dereference
                        //
                        //                        .addCase(Dereference.class,
                        // this::transformDereference)
                        //
                        //                        // Enums
                        //
                        //                        .addCase(EnumLitExpr.class,
                        // this::transformEnumLit)
                        //                        .addCase(EnumEqExpr.class, this::transformEnumEq)
                        //                        .addCase(EnumNeqExpr.class,
                        // this::transformEnumNeq)
                        .build();
    }

    ////

    public Utils.PredTermFormula toTerm(final Expr<?> expr) {
        try {
            return exprToTerm.get(expr, () -> table.dispatch(expr));
        } catch (final ExecutionException e) {
            throw new AssertionError("Unhandled case: " + expr, e);
        }
    }

    private Utils.PredTermFormula transformRef(final RefExpr<?> expr) {
        final Decl<?> decl = expr.getDecl();
        if (decl instanceof ConstDecl) {
            return transformer.toSymbol(decl);
        } else if (decl instanceof ParamDecl) {
            return (Utils.PredTermFormula) env.eval(DeclSymbol.of(decl));
        } else {
            throw new UnsupportedOperationException("Cannot toTerm reference for: " + decl);
        }
    }

    private Utils.PredTermFormula transformIte(final IteExpr<?> expr) {
        final Utils.PredTermFormula cond = toTerm(expr.getCond());
        final Utils.PredTermFormula thenBranch = toTerm(expr.getThen());
        final Utils.PredTermFormula elseBranch = toTerm(expr.getElse());
        return wrap(ite(cond.asFormula(), thenBranch.asTerm(), elseBranch.asTerm()));
    }

    private Utils.PredTermFormula transformFalse(final FalseExpr expr) {
        return wrap(new IBoolLit(false));
    }

    private Utils.PredTermFormula transformTrue(final TrueExpr expr) {
        return wrap(new IBoolLit(true));
    }

    private Utils.PredTermFormula transformNot(final NotExpr expr) {
        final Utils.PredTermFormula op = toTerm(expr.getOp());
        return wrap(op.asFormula().notSimplify());
    }

    private Utils.PredTermFormula transformImply(final ImplyExpr expr) {
        final Utils.PredTermFormula left = toTerm(expr.getLeftOp());
        final Utils.PredTermFormula right = toTerm(expr.getRightOp());
        return wrap(left.asFormula().impSimplify(right.asFormula()));
    }

    private Utils.PredTermFormula transformIff(final IffExpr expr) {
        final Utils.PredTermFormula left = toTerm(expr.getLeftOp());
        final Utils.PredTermFormula right = toTerm(expr.getRightOp());
        return wrap(left.asFormula().eqvSimplify(right.asFormula()));
    }

    private Utils.PredTermFormula transformXor(final XorExpr expr) {
        final Utils.PredTermFormula left = toTerm(expr.getLeftOp());
        final Utils.PredTermFormula right = toTerm(expr.getRightOp());
        return wrap(left.asFormula().eqvSimplify(right.asFormula()).notSimplify());
    }

    private Utils.PredTermFormula transformAnd(final AndExpr expr) {
        return wrap(
                and(
                        getIterable(
                                expr.getOps().stream()
                                        .map(this::toTerm)
                                        .map(Utils.PredTermFormula::asFormula)
                                        .toList())));
    }

    private Utils.PredTermFormula transformOr(final OrExpr expr) {
        return wrap(
                or(
                        getIterable(
                                expr.getOps().stream()
                                        .map(this::toTerm)
                                        .map(Utils.PredTermFormula::asFormula)
                                        .toList())));
    }

    private Utils.PredTermFormula transformExists(final ExistsExpr expr) {
        throw new UnsupportedOperationException("Exists not yet supported for Princess/Eldarica.");
    }

    private Utils.PredTermFormula transformForall(final ForallExpr expr) {
        throw new UnsupportedOperationException("Forall not yet supported for Princess/Eldarica.");
    }

    // INTEGERS

    private Utils.PredTermFormula transformIntLit(final IntLitExpr expr) {
        return wrap(new IIntLit(IdealInt.apply(expr.getValue())));
    }

    private Utils.PredTermFormula transformIntAdd(final IntAddExpr expr) {
        final List<ITerm> terms =
                expr.getOps().stream()
                        .map(this::toTerm)
                        .map(Utils.PredTermFormula::asTerm)
                        .toList();
        return wrap(sum(getIterable(terms)));
    }

    private Utils.PredTermFormula transformIntSub(final IntSubExpr expr) {
        final ITerm left = toTerm(expr.getLeftOp()).asTerm();
        final ITerm right = toTerm(expr.getRightOp()).asTerm();
        return wrap(left.$minus(right));
    }

    private Utils.PredTermFormula transformIntPos(final IntPosExpr expr) {
        return toTerm(expr.getOp()); // Unary plus is a no-op
    }

    private Utils.PredTermFormula transformIntNeg(final IntNegExpr expr) {
        final ITerm op = toTerm(expr.getOp()).asTerm();
        return wrap(op.unary_$minus());
    }

    private Utils.PredTermFormula transformIntMul(final IntMulExpr expr) {
        return wrap(
                expr.getOps().stream()
                        .map(this::toTerm)
                        .map(Utils.PredTermFormula::asTerm)
                        .reduce(ap.theories.nia.GroebnerMultiplication::mult)
                        .orElseThrow());
    }

    private Utils.PredTermFormula transformIntDiv(final IntDivExpr expr) {
        final ITerm left = toTerm(expr.getLeftOp()).asTerm();
        final ITerm right = toTerm(expr.getRightOp()).asTerm();
        return wrap(ap.theories.nia.GroebnerMultiplication.eDivWithSpecialZero(left, right));
    }

    private Utils.PredTermFormula transformIntMod(final IntModExpr expr) {
        final ITerm left = toTerm(expr.getLeftOp()).asTerm();
        final ITerm right = toTerm(expr.getRightOp()).asTerm();
        return wrap(ap.theories.nia.GroebnerMultiplication.eModWithSpecialZero(left, right));
    }

    private Utils.PredTermFormula transformIntRem(final IntRemExpr expr) {
        // Princess does not differentiate Mod vs. Rem — use mod for both for now
        final ITerm left = toTerm(expr.getLeftOp()).asTerm();
        final ITerm right = toTerm(expr.getRightOp()).asTerm();
        final IFormula cond = toTerm(Lt(expr.getLeftOp(), Int(0))).asFormula();
        return wrap(
                ite(
                        cond,
                        ap.theories.nia.GroebnerMultiplication.eModWithSpecialZero(left, right)
                                .unary_$minus(),
                        ap.theories.nia.GroebnerMultiplication.eModWithSpecialZero(left, right)));
    }

    private Utils.PredTermFormula transformIntEq(final IntEqExpr expr) {
        final ITerm left = toTerm(expr.getLeftOp()).asTerm();
        final ITerm right = toTerm(expr.getRightOp()).asTerm();
        return wrap(left.$eq$eq$eq(right));
    }

    private Utils.PredTermFormula transformIntNeq(final IntNeqExpr expr) {
        final ITerm left = toTerm(expr.getLeftOp()).asTerm();
        final ITerm right = toTerm(expr.getRightOp()).asTerm();
        return wrap(left.$eq$eq$eq(right).notSimplify());
    }

    private Utils.PredTermFormula transformIntGeq(final IntGeqExpr expr) {
        final ITerm left = toTerm(expr.getLeftOp()).asTerm();
        final ITerm right = toTerm(expr.getRightOp()).asTerm();
        return wrap(left.$greater$eq(right));
    }

    private Utils.PredTermFormula transformIntGt(final IntGtExpr expr) {
        final ITerm left = toTerm(expr.getLeftOp()).asTerm();
        final ITerm right = toTerm(expr.getRightOp()).asTerm();
        return wrap(left.$greater(right));
    }

    private Utils.PredTermFormula transformIntLeq(final IntLeqExpr expr) {
        final ITerm left = toTerm(expr.getLeftOp()).asTerm();
        final ITerm right = toTerm(expr.getRightOp()).asTerm();
        return wrap(left.$less$eq(right));
    }

    private Utils.PredTermFormula transformIntLt(final IntLtExpr expr) {
        final ITerm left = toTerm(expr.getLeftOp()).asTerm();
        final ITerm right = toTerm(expr.getRightOp()).asTerm();
        return wrap(left.$less(right));
    }

    // BitVectors

    public Utils.PredTermFormula transformBvLit(BvLitExpr expr) {
        ITerm term =
                ModuloArithmetic$.MODULE$.bv(
                        expr.getType().getSize(),
                        IdealInt.apply(BvUtils.neutralBvLitExprToBigInteger(expr)));
        return wrap(term);
    }

    public Utils.PredTermFormula transformBvConcat(BvConcatExpr expr) {
        ITerm term =
                ModuloArithmetic$.MODULE$.concat(
                        toTerm(expr.getOps().get(0)).asTerm(),
                        toTerm(expr.getOps().get(1)).asTerm());
        return wrap(term);
    }

    public Utils.PredTermFormula transformBvExtract(BvExtractExpr expr) {
        ITerm term =
                ModuloArithmetic$.MODULE$.extract(
                        expr.getFrom().getValue().intValue(),
                        expr.getUntil().getValue().intValue(),
                        toTerm(expr.getOps().get(0)).asTerm());
        return wrap(term);
    }

    public Utils.PredTermFormula transformBvZExt(BvZExtExpr expr) {
        ITerm term =
                ModuloArithmetic$.MODULE$.zero_extend(
                        expr.getExtendType().getSize() - expr.getOp().getType().getSize(),
                        toTerm(expr.getOps().get(0)).asTerm());
        return wrap(term);
    }

    public Utils.PredTermFormula transformBvSExt(BvSExtExpr expr) {
        ITerm term =
                ModuloArithmetic$.MODULE$.sign_extend(
                        expr.getExtendType().getSize() - expr.getOp().getType().getSize(),
                        toTerm(expr.getOps().get(0)).asTerm());
        return wrap(term);
    }

    public Utils.PredTermFormula transformBvAdd(BvAddExpr expr) {
        ITerm term =
                ModuloArithmetic$.MODULE$.bvadd(
                        toTerm(expr.getOps().get(0)).asTerm(),
                        toTerm(expr.getOps().get(1)).asTerm());
        return wrap(term);
    }

    public Utils.PredTermFormula transformBvSub(BvSubExpr expr) {
        ITerm term =
                ModuloArithmetic$.MODULE$.bvsub(
                        toTerm(expr.getOps().get(0)).asTerm(),
                        toTerm(expr.getOps().get(1)).asTerm());
        return wrap(term);
    }

    public Utils.PredTermFormula transformBvPos(BvPosExpr expr) {
        return toTerm(expr.getOps().get(0));
    }

    public Utils.PredTermFormula transformBvToInt(BvToIntExpr expr) {
        if (expr.isSigned()) {
            var size = expr.getOp().getType().getSize();
            return toTerm(
                    Ite(
                            Geq(
                                    expr.getOp(),
                                    BvUtils.bigIntegerToNeutralBvLitExpr(BigInteger.ZERO, size)),
                            expr.withSignedness(false),
                            Sub(expr.withSignedness(false), Int(BigInteger.ONE.shiftLeft(size)))));
        }
        return wrap(
                IExpression.toFunApplier(ModuloArithmetic$.MODULE$.int_cast())
                        .apply(toSeq(toTerm(expr.getOps().get(0)).asTerm())));
    }

    public Utils.PredTermFormula transformBvSignChange(BvSignChangeExpr expr) {
        ITerm term = ModuloArithmetic$.MODULE$.bvneg(toTerm(expr.getOps().get(0)).asTerm());
        return wrap(term);
    }

    public Utils.PredTermFormula transformBvNeg(BvNegExpr expr) {
        ITerm term = ModuloArithmetic$.MODULE$.bvneg(toTerm(expr.getOps().get(0)).asTerm());
        return wrap(term);
    }

    public Utils.PredTermFormula transformBvMul(BvMulExpr expr) {
        ITerm term =
                ModuloArithmetic$.MODULE$.bvmul(
                        toTerm(expr.getOps().get(0)).asTerm(),
                        toTerm(expr.getOps().get(1)).asTerm());
        return wrap(term);
    }

    public Utils.PredTermFormula transformBvUDiv(BvUDivExpr expr) {
        ITerm term =
                ModuloArithmetic$.MODULE$.bvudiv(
                        toTerm(expr.getOps().get(0)).asTerm(),
                        toTerm(expr.getOps().get(1)).asTerm());
        return wrap(term);
    }

    public Utils.PredTermFormula transformBvSDiv(BvSDivExpr expr) {
        ITerm term =
                ModuloArithmetic$.MODULE$.bvsdiv(
                        toTerm(expr.getOps().get(0)).asTerm(),
                        toTerm(expr.getOps().get(1)).asTerm());
        return wrap(term);
    }

    public Utils.PredTermFormula transformBvSMod(BvSModExpr expr) {
        ITerm term =
                ModuloArithmetic$.MODULE$.bvsmod(
                        toTerm(expr.getOps().get(0)).asTerm(),
                        toTerm(expr.getOps().get(1)).asTerm());
        return wrap(term);
    }

    public Utils.PredTermFormula transformBvURem(BvURemExpr expr) {
        ITerm term =
                ModuloArithmetic$.MODULE$.bvurem(
                        toTerm(expr.getOps().get(0)).asTerm(),
                        toTerm(expr.getOps().get(1)).asTerm());
        return wrap(term);
    }

    public Utils.PredTermFormula transformBvSRem(BvSRemExpr expr) {
        ITerm term =
                ModuloArithmetic$.MODULE$.bvsrem(
                        toTerm(expr.getOps().get(0)).asTerm(),
                        toTerm(expr.getOps().get(1)).asTerm());
        return wrap(term);
    }

    public Utils.PredTermFormula transformBvAnd(BvAndExpr expr) {
        ITerm term =
                ModuloArithmetic$.MODULE$.bvand(
                        toTerm(expr.getOps().get(0)).asTerm(),
                        toTerm(expr.getOps().get(1)).asTerm());
        return wrap(term);
    }

    public Utils.PredTermFormula transformBvOr(BvOrExpr expr) {
        ITerm term =
                ModuloArithmetic$.MODULE$.bvor(
                        toTerm(expr.getOps().get(0)).asTerm(),
                        toTerm(expr.getOps().get(1)).asTerm());
        return wrap(term);
    }

    public Utils.PredTermFormula transformBvXor(BvXorExpr expr) {
        ITerm term =
                ModuloArithmetic$.MODULE$.bvxor(
                        toTerm(expr.getOps().get(0)).asTerm(),
                        toTerm(expr.getOps().get(1)).asTerm());
        return wrap(term);
    }

    public Utils.PredTermFormula transformBvNot(BvNotExpr expr) {
        ITerm term = ModuloArithmetic$.MODULE$.bvnot(toTerm(expr.getOps().get(0)).asTerm());
        return wrap(term);
    }

    public Utils.PredTermFormula transformBvShiftLeft(BvShiftLeftExpr expr) {
        ITerm term =
                ModuloArithmetic$.MODULE$.bvshl(
                        toTerm(expr.getOps().get(0)).asTerm(),
                        toTerm(expr.getOps().get(1)).asTerm());
        return wrap(term);
    }

    public Utils.PredTermFormula transformBvArithShiftRight(BvArithShiftRightExpr expr) {
        ITerm term =
                ModuloArithmetic$.MODULE$.bvashr(
                        toTerm(expr.getOps().get(0)).asTerm(),
                        toTerm(expr.getOps().get(1)).asTerm());
        return wrap(term);
    }

    public Utils.PredTermFormula transformBvLogicShiftRight(BvLogicShiftRightExpr expr) {
        ITerm term =
                ModuloArithmetic$.MODULE$.bvlshr(
                        toTerm(expr.getOps().get(0)).asTerm(),
                        toTerm(expr.getOps().get(1)).asTerm());
        return wrap(term);
    }

    public Utils.PredTermFormula transformBvRotateLeft(BvRotateLeftExpr expr) {
        throw new UnsupportedOperationException("Princess does not support bitvector rotation.");
    }

    public Utils.PredTermFormula transformBvRotateRight(BvRotateRightExpr expr) {
        throw new UnsupportedOperationException("Princess does not support bitvector rotation.");
    }

    public Utils.PredTermFormula transformBvEq(BvEqExpr expr) {
        IFormula formula =
                toTerm(expr.getOps().get(0))
                        .asTerm()
                        .$eq$eq$eq(toTerm(expr.getOps().get(1)).asTerm());
        return wrap(formula);
    }

    public Utils.PredTermFormula transformBvNeq(BvNeqExpr expr) {
        IFormula formula =
                toTerm(expr.getOps().get(0))
                        .asTerm()
                        .$eq$eq$eq(toTerm(expr.getOps().get(1)).asTerm())
                        .notSimplify();
        return wrap(formula);
    }

    public Utils.PredTermFormula transformBvUGeq(BvUGeqExpr expr) {
        IFormula formula =
                ModuloArithmetic$.MODULE$.bvuge(
                        toTerm(expr.getOps().get(0)).asTerm(),
                        toTerm(expr.getOps().get(1)).asTerm());
        return wrap(formula);
    }

    public Utils.PredTermFormula transformBvUGt(BvUGtExpr expr) {
        IFormula formula =
                ModuloArithmetic$.MODULE$.bvugt(
                        toTerm(expr.getOps().get(0)).asTerm(),
                        toTerm(expr.getOps().get(1)).asTerm());
        return wrap(formula);
    }

    public Utils.PredTermFormula transformBvULeq(BvULeqExpr expr) {
        IFormula formula =
                ModuloArithmetic$.MODULE$.bvule(
                        toTerm(expr.getOps().get(0)).asTerm(),
                        toTerm(expr.getOps().get(1)).asTerm());
        return wrap(formula);
    }

    public Utils.PredTermFormula transformBvULt(BvULtExpr expr) {
        IFormula formula =
                ModuloArithmetic$.MODULE$.bvult(
                        toTerm(expr.getOps().get(0)).asTerm(),
                        toTerm(expr.getOps().get(1)).asTerm());
        return wrap(formula);
    }

    public Utils.PredTermFormula transformBvSGeq(BvSGeqExpr expr) {
        IFormula formula =
                ModuloArithmetic$.MODULE$.bvsge(
                        toTerm(expr.getOps().get(0)).asTerm(),
                        toTerm(expr.getOps().get(1)).asTerm());
        return wrap(formula);
    }

    public Utils.PredTermFormula transformBvSGt(BvSGtExpr expr) {
        IFormula formula =
                ModuloArithmetic$.MODULE$.bvsgt(
                        toTerm(expr.getOps().get(0)).asTerm(),
                        toTerm(expr.getOps().get(1)).asTerm());
        return wrap(formula);
    }

    public Utils.PredTermFormula transformBvSLeq(BvSLeqExpr expr) {
        IFormula formula =
                ModuloArithmetic$.MODULE$.bvsle(
                        toTerm(expr.getOps().get(0)).asTerm(),
                        toTerm(expr.getOps().get(1)).asTerm());
        return wrap(formula);
    }

    public Utils.PredTermFormula transformBvSLt(BvSLtExpr expr) {
        IFormula formula =
                ModuloArithmetic$.MODULE$.bvslt(
                        toTerm(expr.getOps().get(0)).asTerm(),
                        toTerm(expr.getOps().get(1)).asTerm());
        return wrap(formula);
    }

    // functions

    public Utils.PredTermFormula transformFuncApp(FuncAppExpr<?, ?> expr) {
        final Tuple2<Expr<?>, List<Expr<?>>> funcAndArgs = extractFuncAndArgs(expr);
        final Expr<?> func = funcAndArgs.get1();
        if (func instanceof RefExpr) {
            final RefExpr<?> ref = (RefExpr<?>) func;
            final Decl<?> decl = ref.getDecl();
            final Predicate pred = transformer.toSymbol(decl).asPredicate();
            final List<Expr<?>> args = funcAndArgs.get2();
            final Seq<ITerm> argTerms =
                    toSeq(
                            args.stream()
                                    .map(this::toTerm)
                                    .map(Utils.PredTermFormula::asTerm)
                                    .toList());

            return wrap(IExpression.toPredApplier(pred).apply(argTerms));
        } else {
            throw new UnsupportedOperationException(
                    "Higher order functions are not supported: " + func);
        }
    }

    // arrays

    public Utils.PredTermFormula transformArrayRead(ArrayReadExpr<?, ?> expr) {
        ITerm array = toTerm(expr.getOps().get(0)).asTerm();
        ITerm index = toTerm(expr.getOps().get(1)).asTerm();
        ExtArray.ArraySort arraySort = (ExtArray.ArraySort) Sort$.MODULE$.sortOf(array);
        ITerm term =
                IExpression.toFunApplier(arraySort.theory().select())
                        .apply(toSeq(List.of(array, index)));
        return wrap(term);
    }

    public Utils.PredTermFormula transformArrayWrite(ArrayWriteExpr<?, ?> expr) {
        ITerm array = toTerm(expr.getOps().get(0)).asTerm();
        ITerm index = toTerm(expr.getOps().get(1)).asTerm();
        ITerm value = toTerm(expr.getOps().get(2)).asTerm();
        ExtArray.ArraySort arraySort = (ExtArray.ArraySort) Sort$.MODULE$.sortOf(array);
        ITerm term =
                IExpression.toFunApplier(arraySort.theory().store())
                        .apply(toSeq(List.of(array, index, value)));
        return wrap(term);
    }

    public Utils.PredTermFormula transformArrayEq(ArrayEqExpr<?, ?> expr) {
        ITerm left = toTerm(expr.getOps().get(0)).asTerm();
        ITerm right = toTerm(expr.getOps().get(1)).asTerm();
        IFormula formula = left.$eq$eq$eq(right);
        return wrap(formula);
    }

    public Utils.PredTermFormula transformArrayNeq(ArrayNeqExpr<?, ?> expr) {
        ITerm left = toTerm(expr.getOps().get(0)).asTerm();
        ITerm right = toTerm(expr.getOps().get(1)).asTerm();
        IFormula formula = left.$eq$eq$eq(right).notSimplify();
        return wrap(formula);
    }

    public Utils.PredTermFormula transformArrayLit(ArrayLitExpr<?, ?> expr) {
        ITerm elseElem = toTerm(expr.getElseElem()).asTerm();

        ExtArray.ArraySort arraySort = (ExtArray.ArraySort) transformer.toSort(expr.getType());
        final IFunction constArrayOp = arraySort.theory().constArray();
        ITerm term = IExpression.toFunApplier(constArrayOp).apply(toSeq(elseElem));
        final var store = IExpression.toFunApplier(arraySort.theory().store());
        for (Tuple2<? extends LitExpr<?>, ? extends LitExpr<?>> element : expr.getElements()) {
            term =
                    store.apply(
                            toSeq(
                                    List.of(
                                            term,
                                            toTerm(element.get1()).asTerm(),
                                            toTerm(element.get2()).asTerm())));
        }
        return wrap(term);
    }

    public Utils.PredTermFormula transformArrayInit(ArrayInitExpr<?, ?> expr) {
        ITerm elseElem = toTerm(expr.getElseElem()).asTerm();

        ExtArray.ArraySort arraySort = (ExtArray.ArraySort) transformer.toSort(expr.getType());
        final IFunction constArrayOp = arraySort.theory().constArray();
        ITerm term = IExpression.toFunApplier(constArrayOp).apply(toSeq(elseElem));
        final var store = IExpression.toFunApplier(arraySort.theory().store());
        for (Tuple2<? extends Expr<?>, ? extends Expr<?>> element : expr.getElements()) {
            term =
                    store.apply(
                            toSeq(
                                    List.of(
                                            term,
                                            toTerm(element.get1()).asTerm(),
                                            toTerm(element.get2()).asTerm())));
        }
        return wrap(term);
    }
}
