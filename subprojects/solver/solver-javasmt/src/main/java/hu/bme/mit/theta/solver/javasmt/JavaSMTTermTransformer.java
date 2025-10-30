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

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;
import static com.google.common.base.Preconditions.checkState;
import static com.google.common.collect.ImmutableList.toImmutableList;
import static hu.bme.mit.theta.core.decl.Decls.Const;
import static hu.bme.mit.theta.core.decl.Decls.Param;
import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Eq;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Exists;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.False;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Forall;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.True;
import static hu.bme.mit.theta.core.type.fptype.FpExprs.FpAssign;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;
import static hu.bme.mit.theta.core.type.rattype.RatExprs.Rat;

import com.google.common.collect.Lists;
import hu.bme.mit.theta.common.QuadFunction;
import hu.bme.mit.theta.common.TernaryOperator;
import hu.bme.mit.theta.common.TriFunction;
import hu.bme.mit.theta.common.Tuple2;
import hu.bme.mit.theta.common.container.Containers;
import hu.bme.mit.theta.core.decl.Decl;
import hu.bme.mit.theta.core.decl.ParamDecl;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.arraytype.ArrayInitExpr;
import hu.bme.mit.theta.core.type.arraytype.ArrayLitExpr;
import hu.bme.mit.theta.core.type.arraytype.ArrayType;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.type.bvtype.BvExtractExpr;
import hu.bme.mit.theta.core.type.bvtype.BvLitExpr;
import hu.bme.mit.theta.core.type.bvtype.BvSExtExpr;
import hu.bme.mit.theta.core.type.bvtype.BvType;
import hu.bme.mit.theta.core.type.bvtype.BvZExtExpr;
import hu.bme.mit.theta.core.type.enumtype.EnumLitExpr;
import hu.bme.mit.theta.core.type.enumtype.EnumType;
import hu.bme.mit.theta.core.type.fptype.FpFromBvExpr;
import hu.bme.mit.theta.core.type.fptype.FpLitExpr;
import hu.bme.mit.theta.core.type.fptype.FpRoundingMode;
import hu.bme.mit.theta.core.type.fptype.FpToBvExpr;
import hu.bme.mit.theta.core.type.fptype.FpToFpExpr;
import hu.bme.mit.theta.core.type.fptype.FpType;
import hu.bme.mit.theta.core.type.functype.FuncExprs;
import hu.bme.mit.theta.core.type.functype.FuncType;
import hu.bme.mit.theta.core.type.inttype.IntLitExpr;
import hu.bme.mit.theta.core.utils.BvUtils;
import hu.bme.mit.theta.core.utils.TypeUtils;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.function.BiFunction;
import java.util.function.BinaryOperator;
import java.util.function.Function;
import java.util.function.Supplier;
import java.util.function.UnaryOperator;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.stream.Collectors;
import org.sosy_lab.common.rationals.Rational;
import org.sosy_lab.java_smt.api.BitvectorFormula;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.FloatingPointFormula;
import org.sosy_lab.java_smt.api.FloatingPointNumber;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.FormulaType.ArrayFormulaType;
import org.sosy_lab.java_smt.api.FormulaType.BitvectorType;
import org.sosy_lab.java_smt.api.FormulaType.FloatingPointType;
import org.sosy_lab.java_smt.api.FunctionDeclaration;
import org.sosy_lab.java_smt.api.FunctionDeclarationKind;
import org.sosy_lab.java_smt.api.Model;
import org.sosy_lab.java_smt.api.QuantifiedFormulaManager.Quantifier;
import org.sosy_lab.java_smt.api.SolverContext;
import org.sosy_lab.java_smt.api.visitors.FormulaVisitor;

final class JavaSMTTermTransformer {

    private static final String PARAM_NAME_FORMAT = "_p%d";

    private final JavaSMTSymbolTable symbolTable;
    private final SolverContext context;
    private final Map<
                    Tuple2<FunctionDeclarationKind, Integer>,
                    QuadFunction<Formula, List<Formula>, Model, List<Decl<?>>, Expr<?>>>
            environment;
    private final Map<
                    Tuple2<String, Integer>,
                    QuadFunction<Formula, List<Formula>, Model, List<Decl<?>>, Expr<?>>>
            otherFuncs;

    public JavaSMTTermTransformer(final JavaSMTSymbolTable symbolTable, SolverContext context) {
        this.symbolTable = symbolTable;
        this.context = context;

        environment = Containers.createMap();
        otherFuncs = Containers.createMap();
        addEnvFunc(
                FunctionDeclarationKind.AND,
                exprMultiaryOperator(hu.bme.mit.theta.core.type.booltype.AndExpr::create));
        //        addEnvFunc("false",
        // exprNullaryOperator(hu.bme.mit.theta.core.type.booltype.FalseExpr::getInstance));
        //        addEnvFunc("true",
        // exprNullaryOperator(hu.bme.mit.theta.core.type.booltype.TrueExpr::getInstance));
        addEnvFunc(
                FunctionDeclarationKind.IFF,
                exprBinaryOperator(hu.bme.mit.theta.core.type.booltype.IffExpr::create));
        addEnvFunc(
                FunctionDeclarationKind.NOT,
                exprUnaryOperator(hu.bme.mit.theta.core.type.booltype.NotExpr::create));
        addEnvFunc(
                FunctionDeclarationKind.IMPLIES,
                exprBinaryOperator(hu.bme.mit.theta.core.type.booltype.ImplyExpr::create));
        addEnvFunc(
                FunctionDeclarationKind.XOR,
                exprBinaryOperator(hu.bme.mit.theta.core.type.booltype.XorExpr::create));
        addEnvFunc(
                FunctionDeclarationKind.OR,
                exprMultiaryOperator(hu.bme.mit.theta.core.type.booltype.OrExpr::create));
        addEnvFunc(
                FunctionDeclarationKind.ITE,
                exprTernaryOperator(hu.bme.mit.theta.core.type.anytype.IteExpr::create));
        //        addEnvFunc("if",
        // exprTernaryOperator(hu.bme.mit.theta.core.type.anytype.IteExpr::create));
        //        addEnvFunc("prime",
        // exprUnaryOperator(hu.bme.mit.theta.core.type.anytype.PrimeExpr::of));
        addEnvFunc(
                FunctionDeclarationKind.EQ,
                exprBinaryOperator(
                        (expr, expr2) ->
                                expr.getType() instanceof FpType
                                        ? FpAssign((Expr<FpType>) expr, (Expr<FpType>) expr2)
                                        : Eq(expr, expr2)));
        addEnvFunc(
                FunctionDeclarationKind.GTE,
                exprBinaryOperator(hu.bme.mit.theta.core.type.abstracttype.AbstractExprs::Geq));
        addEnvFunc(
                FunctionDeclarationKind.GT,
                exprBinaryOperator(hu.bme.mit.theta.core.type.abstracttype.AbstractExprs::Gt));
        addEnvFunc(
                FunctionDeclarationKind.LTE,
                exprBinaryOperator(hu.bme.mit.theta.core.type.abstracttype.AbstractExprs::Leq));
        addEnvFunc(
                FunctionDeclarationKind.LT,
                exprBinaryOperator(hu.bme.mit.theta.core.type.abstracttype.AbstractExprs::Lt));
        addEnvFunc(
                FunctionDeclarationKind.ADD,
                exprBinaryOperator(hu.bme.mit.theta.core.type.abstracttype.AbstractExprs::Add));
        addEnvFunc(
                FunctionDeclarationKind.SUB,
                exprBinaryOperator(hu.bme.mit.theta.core.type.abstracttype.AbstractExprs::Sub));
        addEnvFunc(
                FunctionDeclarationKind.ADD,
                exprUnaryOperator(hu.bme.mit.theta.core.type.abstracttype.AbstractExprs::Pos));
        addEnvFunc(
                FunctionDeclarationKind.UMINUS,
                exprUnaryOperator(hu.bme.mit.theta.core.type.abstracttype.AbstractExprs::Neg));
        addEnvFunc(
                FunctionDeclarationKind.MUL,
                exprBinaryOperator(hu.bme.mit.theta.core.type.abstracttype.AbstractExprs::Mul));
        addEnvFunc(
                FunctionDeclarationKind.DIV,
                exprBinaryOperator(hu.bme.mit.theta.core.type.abstracttype.AbstractExprs::Div));
        addEnvFunc(
                FunctionDeclarationKind.FLOOR,
                exprUnaryOperator(hu.bme.mit.theta.core.type.rattype.RatToIntExpr::create));
        addEnvFunc(
                FunctionDeclarationKind.FP_ROUND_TO_INTEGRAL,
                exprUnaryOperator(hu.bme.mit.theta.core.type.rattype.RatToIntExpr::create));
        //        addEnvFunc("div",
        // exprBinaryOperator(hu.bme.mit.theta.core.type.inttype.IntDivExpr::create));
        addEnvFunc(
                FunctionDeclarationKind.TO_REAL,
                exprUnaryOperator(hu.bme.mit.theta.core.type.inttype.IntToRatExpr::create));
        addEnvFunc(
                FunctionDeclarationKind.MODULO,
                exprBinaryOperator(hu.bme.mit.theta.core.type.inttype.IntModExpr::create));
        //        addEnvFunc("rem",
        // exprBinaryOperator(hu.bme.mit.theta.core.type.inttype.IntRemExpr::create));
        addEnvFunc(
                FunctionDeclarationKind.FP_ADD,
                exprFpMultiaryOperator(hu.bme.mit.theta.core.type.fptype.FpAddExpr::create));
        addEnvFunc(
                FunctionDeclarationKind.FP_SUB,
                exprFpBinaryOperator(hu.bme.mit.theta.core.type.fptype.FpSubExpr::create));
        //        addEnvFunc("fp.pos",
        // exprUnaryOperator(hu.bme.mit.theta.core.type.fptype.FpPosExpr::create));
        addEnvFunc(
                FunctionDeclarationKind.FP_NEG,
                exprUnaryOperator(hu.bme.mit.theta.core.type.fptype.FpNegExpr::create));
        addEnvFunc(
                FunctionDeclarationKind.FP_MUL,
                exprFpMultiaryOperator(hu.bme.mit.theta.core.type.fptype.FpMulExpr::create));
        addEnvFunc(
                FunctionDeclarationKind.FP_DIV,
                exprFpBinaryOperator(hu.bme.mit.theta.core.type.fptype.FpDivExpr::create));
        addOtherFunc(
                "fp.rem", exprBinaryOperator(hu.bme.mit.theta.core.type.fptype.FpRemExpr::create));
        addOtherFunc(
                "fprem", exprBinaryOperator(hu.bme.mit.theta.core.type.fptype.FpRemExpr::create));
        addEnvFunc(
                FunctionDeclarationKind.FP_ABS,
                exprUnaryOperator(hu.bme.mit.theta.core.type.fptype.FpAbsExpr::create));
        addEnvFunc(
                FunctionDeclarationKind.FP_LE,
                exprBinaryOperator(hu.bme.mit.theta.core.type.fptype.FpLeqExpr::create));
        addEnvFunc(
                FunctionDeclarationKind.FP_LT,
                exprBinaryOperator(hu.bme.mit.theta.core.type.fptype.FpLtExpr::create));
        addEnvFunc(
                FunctionDeclarationKind.FP_GE,
                exprBinaryOperator(hu.bme.mit.theta.core.type.fptype.FpGeqExpr::create));
        addEnvFunc(
                FunctionDeclarationKind.FP_GT,
                exprBinaryOperator(hu.bme.mit.theta.core.type.fptype.FpGtExpr::create));
        addEnvFunc(
                FunctionDeclarationKind.FP_EQ,
                exprBinaryOperator(hu.bme.mit.theta.core.type.fptype.FpEqExpr::create));
        addEnvFunc(
                FunctionDeclarationKind.FP_IS_NAN,
                exprUnaryOperator(hu.bme.mit.theta.core.type.fptype.FpIsNanExpr::create));
        //        addEnvFunc("fp.isNaN",
        // exprUnaryOperator(hu.bme.mit.theta.core.type.fptype.FpIsNanExpr::create));
        addEnvFunc(
                FunctionDeclarationKind.FP_IS_INF,
                exprUnaryOperator(hu.bme.mit.theta.core.type.fptype.FpIsInfiniteExpr::create));
        //        addEnvFunc("fp.isInfinite",
        // exprUnaryOperator(hu.bme.mit.theta.core.type.fptype.FpIsInfiniteExpr::create));
        addEnvFunc(
                FunctionDeclarationKind.FP_ROUND_TO_INTEGRAL,
                exprFpUnaryOperator(
                        hu.bme.mit.theta.core.type.fptype.FpRoundToIntegralExpr::create));
        //        addEnvFunc("fp.roundToIntegral",
        // exprFpUnaryOperator(hu.bme.mit.theta.core.type.fptype.FpRoundToIntegralExpr::create));
        addEnvFunc(
                FunctionDeclarationKind.FP_SQRT,
                exprFpUnaryOperator(hu.bme.mit.theta.core.type.fptype.FpSqrtExpr::create));
        addEnvFunc(
                FunctionDeclarationKind.FP_MAX,
                exprBinaryOperator(hu.bme.mit.theta.core.type.fptype.FpMaxExpr::create));
        addEnvFunc(
                FunctionDeclarationKind.FP_MIN,
                exprBinaryOperator(hu.bme.mit.theta.core.type.fptype.FpMinExpr::create));
        addEnvFunc(
                FunctionDeclarationKind.BV_CONCAT,
                exprMultiaryOperator(hu.bme.mit.theta.core.type.bvtype.BvConcatExpr::create));
        //        addEnvFunc("concat",
        // exprMultiaryOperator(hu.bme.mit.theta.core.type.bvtype.BvConcatExpr::create));
        addEnvFunc(
                FunctionDeclarationKind.BV_ADD,
                exprMultiaryOperator(hu.bme.mit.theta.core.type.bvtype.BvAddExpr::create));
        addEnvFunc(
                FunctionDeclarationKind.BV_SUB,
                exprBinaryOperator(hu.bme.mit.theta.core.type.bvtype.BvSubExpr::create));
        //        addEnvFunc("bvpos",
        // exprUnaryOperator(hu.bme.mit.theta.core.type.bvtype.BvPosExpr::create));
        addEnvFunc(
                FunctionDeclarationKind.BV_NEG,
                exprUnaryOperator(hu.bme.mit.theta.core.type.bvtype.BvNegExpr::create));
        addOtherFunc(
                "bv2int",
                exprUnaryOperator(
                        t -> hu.bme.mit.theta.core.type.bvtype.BvToIntExpr.create(t, false)));
        addEnvFunc(
                FunctionDeclarationKind.BV_MUL,
                exprMultiaryOperator(hu.bme.mit.theta.core.type.bvtype.BvMulExpr::create));
        addEnvFunc(
                FunctionDeclarationKind.BV_UDIV,
                exprBinaryOperator(hu.bme.mit.theta.core.type.bvtype.BvUDivExpr::create));
        addEnvFunc(
                FunctionDeclarationKind.BV_SDIV,
                exprBinaryOperator(hu.bme.mit.theta.core.type.bvtype.BvSDivExpr::create));
        addOtherFunc(
                "bvsmod", exprBinaryOperator(hu.bme.mit.theta.core.type.bvtype.BvSModExpr::create));
        addEnvFunc(
                FunctionDeclarationKind.BV_UREM,
                exprBinaryOperator(hu.bme.mit.theta.core.type.bvtype.BvURemExpr::create));
        addEnvFunc(
                FunctionDeclarationKind.BV_SREM,
                exprBinaryOperator(hu.bme.mit.theta.core.type.bvtype.BvSRemExpr::create));
        addEnvFunc(
                FunctionDeclarationKind.BV_OR,
                exprMultiaryOperator(hu.bme.mit.theta.core.type.bvtype.BvOrExpr::create));
        addEnvFunc(
                FunctionDeclarationKind.BV_AND,
                exprMultiaryOperator(hu.bme.mit.theta.core.type.bvtype.BvAndExpr::create));
        addEnvFunc(
                FunctionDeclarationKind.BV_XOR,
                exprMultiaryOperator(hu.bme.mit.theta.core.type.bvtype.BvXorExpr::create));
        addEnvFunc(
                FunctionDeclarationKind.BV_NOT,
                exprUnaryOperator(hu.bme.mit.theta.core.type.bvtype.BvNotExpr::create));
        addEnvFunc(
                FunctionDeclarationKind.BV_SHL,
                exprBinaryOperator(hu.bme.mit.theta.core.type.bvtype.BvShiftLeftExpr::create));
        addEnvFunc(
                FunctionDeclarationKind.BV_ASHR,
                exprBinaryOperator(
                        hu.bme.mit.theta.core.type.bvtype.BvArithShiftRightExpr::create));
        addEnvFunc(
                FunctionDeclarationKind.BV_LSHR,
                exprBinaryOperator(
                        hu.bme.mit.theta.core.type.bvtype.BvLogicShiftRightExpr::create));
        //        addEnvFunc("bvrol",
        // exprBinaryOperator(hu.bme.mit.theta.core.type.bvtype.BvRotateLeftExpr::create));
        addOtherFunc(
                "ext_rotate_left",
                exprBinaryOperator(hu.bme.mit.theta.core.type.bvtype.BvRotateLeftExpr::create));
        //        addEnvFunc("bvror",
        // exprBinaryOperator(hu.bme.mit.theta.core.type.bvtype.BvRotateRightExpr::create));
        addOtherFunc(
                "ext_rotate_right",
                exprBinaryOperator(hu.bme.mit.theta.core.type.bvtype.BvRotateRightExpr::create));
        addEnvFunc(
                FunctionDeclarationKind.BV_ULT,
                exprBinaryOperator(hu.bme.mit.theta.core.type.bvtype.BvULtExpr::create));
        addEnvFunc(
                FunctionDeclarationKind.BV_ULE,
                exprBinaryOperator(hu.bme.mit.theta.core.type.bvtype.BvULeqExpr::create));
        addEnvFunc(
                FunctionDeclarationKind.BV_UGT,
                exprBinaryOperator(hu.bme.mit.theta.core.type.bvtype.BvUGtExpr::create));
        addEnvFunc(
                FunctionDeclarationKind.BV_UGE,
                exprBinaryOperator(hu.bme.mit.theta.core.type.bvtype.BvUGeqExpr::create));
        addEnvFunc(
                FunctionDeclarationKind.BV_SLT,
                exprBinaryOperator(hu.bme.mit.theta.core.type.bvtype.BvSLtExpr::create));
        addEnvFunc(
                FunctionDeclarationKind.BV_SLE,
                exprBinaryOperator(hu.bme.mit.theta.core.type.bvtype.BvSLeqExpr::create));
        addEnvFunc(
                FunctionDeclarationKind.BV_SGT,
                exprBinaryOperator(hu.bme.mit.theta.core.type.bvtype.BvSGtExpr::create));
        addEnvFunc(
                FunctionDeclarationKind.BV_SGE,
                exprBinaryOperator(hu.bme.mit.theta.core.type.bvtype.BvSGeqExpr::create));
        //        addEnvFunc("read",
        // exprBinaryOperator(hu.bme.mit.theta.core.type.arraytype.ArrayReadExpr::create));
        //        addEnvFunc("write",
        // exprTernaryOperator(hu.bme.mit.theta.core.type.arraytype.ArrayWriteExpr::create));
        addEnvFunc(
                FunctionDeclarationKind.SELECT,
                exprBinaryOperator(hu.bme.mit.theta.core.type.arraytype.ArrayReadExpr::create));
        addEnvFunc(
                FunctionDeclarationKind.STORE,
                exprTernaryOperator(hu.bme.mit.theta.core.type.arraytype.ArrayWriteExpr::create));

        environment.put(
                Tuple2.of(FunctionDeclarationKind.FP_FROM_IEEEBV, 1),
                (term, args, model, vars) -> {
                    FloatingPointType type =
                            (FloatingPointType)
                                    context.getFormulaManager()
                                            .getFormulaType((FloatingPointFormula) term);
                    final var roundingmode = getRoundingMode(args.get(0).toString());
                    final Expr<BvType> op = (Expr<BvType>) transform(args.get(1), model, vars);
                    return FpFromBvExpr.of(
                            roundingmode,
                            op,
                            FpType.of(type.getExponentSize(), type.getMantissaSize() + 1),
                            true);
                });
        environment.put(
                Tuple2.of(FunctionDeclarationKind.FP_CASTTO_SBV, 2),
                (term, args, model, vars) -> {
                    BitvectorType type =
                            (BitvectorType)
                                    context.getFormulaManager()
                                            .getFormulaType((BitvectorFormula) term);
                    final var roundingmode = getRoundingMode(args.get(0).toString());
                    final Expr<FpType> op = (Expr<FpType>) transform(args.get(1), model, vars);
                    return FpToBvExpr.of(roundingmode, op, type.getSize(), true);
                });
        environment.put(
                Tuple2.of(FunctionDeclarationKind.FP_CASTTO_UBV, 2),
                (term, args, model, vars) -> {
                    BitvectorType type =
                            (BitvectorType)
                                    context.getFormulaManager()
                                            .getFormulaType((BitvectorFormula) term);
                    final var roundingmode = getRoundingMode(args.get(0).toString());
                    final Expr<FpType> op = (Expr<FpType>) transform(args.get(1), model, vars);
                    return FpToBvExpr.of(roundingmode, op, type.getSize(), false);
                });
        environment.put(
                Tuple2.of(FunctionDeclarationKind.BV_SCASTTO_FP, 2),
                (term, args, model, vars) -> {
                    FloatingPointType type =
                            (FloatingPointType)
                                    context.getFormulaManager()
                                            .getFormulaType((FloatingPointFormula) term);
                    final var roundingmode = getRoundingMode(args.get(0).toString());
                    final Expr<?> op = transform(args.get(1), model, vars);
                    if (op.getType() instanceof FpType) {
                        return FpToFpExpr.of(
                                roundingmode,
                                (Expr<FpType>) op,
                                type.getExponentSize(),
                                type.getMantissaSize() + 1);
                    } else if (op.getType() instanceof BvType) {
                        return FpFromBvExpr.of(
                                roundingmode,
                                (Expr<BvType>) op,
                                FpType.of(type.getExponentSize(), type.getMantissaSize() + 1),
                                false);
                    } else {
                        throw new JavaSMTSolverException("Unsupported:" + op.getType());
                    }
                });
        environment.put(
                Tuple2.of(FunctionDeclarationKind.FP_CASTTO_FP, 2),
                (term, args, model, vars) -> {
                    FloatingPointType type =
                            (FloatingPointType)
                                    context.getFormulaManager()
                                            .getFormulaType((FloatingPointFormula) term);
                    final var roundingmode = getRoundingMode(args.get(0).toString());
                    final Expr<?> op = transform(args.get(1), model, vars);
                    if (op.getType() instanceof FpType) {
                        return FpToFpExpr.of(
                                roundingmode,
                                (Expr<FpType>) op,
                                type.getExponentSize(),
                                type.getMantissaSize() + 1);
                    } else if (op.getType() instanceof BvType) {
                        return FpFromBvExpr.of(
                                roundingmode,
                                (Expr<BvType>) op,
                                FpType.of(type.getExponentSize(), type.getMantissaSize() + 1),
                                false);
                    } else {
                        throw new JavaSMTSolverException("Unsupported:" + op.getType());
                    }
                });
        otherFuncs.put(
                Tuple2.of("to_fp", 1),
                (term, args, model, vars) -> {
                    FloatingPointType type =
                            (FloatingPointType)
                                    context.getFormulaManager()
                                            .getFormulaType((FloatingPointFormula) term);
                    final Expr<BvType> op = (Expr<BvType>) transform(args.get(0), model, vars);
                    return FpFromBvExpr.of(
                            FpRoundingMode.getDefaultRoundingMode(),
                            op,
                            FpType.of(type.getExponentSize(), type.getMantissaSize() + 1),
                            true);
                });

        environment.put(
                Tuple2.of(FunctionDeclarationKind.BV_EXTRACT, 1),
                (term, args, model, vars) -> {
                    final Pattern pattern = Pattern.compile("extract ([0-9]+) ([0-9]+)");
                    final String termStr = term.toString();
                    final Matcher match = pattern.matcher(termStr);
                    if (match.find()) {
                        final int to = Integer.parseInt(match.group(1)) + 1;
                        final int from = Integer.parseInt(match.group(2));
                        final Expr<BvType> op = (Expr<BvType>) transform(args.get(0), model, vars);
                        return BvExtractExpr.of(op, Int(from), Int(to));
                    }
                    throw new JavaSMTSolverException("Not supported: " + term);
                });
        environment.put(
                Tuple2.of(FunctionDeclarationKind.BV_ZERO_EXTENSION, 1),
                (term, args, model, vars) -> {
                    BitvectorType type =
                            (BitvectorType)
                                    context.getFormulaManager()
                                            .getFormulaType((BitvectorFormula) term);
                    final Expr<BvType> op = (Expr<BvType>) transform(args.get(0), model, vars);
                    return BvZExtExpr.of(op, BvType.of(type.getSize()));
                });
        environment.put(
                Tuple2.of(FunctionDeclarationKind.BV_SIGN_EXTENSION, 1),
                (term, args, model, vars) -> {
                    BitvectorType type =
                            (BitvectorType)
                                    context.getFormulaManager()
                                            .getFormulaType((BitvectorFormula) term);
                    final Expr<BvType> op = (Expr<BvType>) transform(args.get(0), model, vars);
                    return BvSExtExpr.of(op, BvType.of(type.getSize()));
                });
        environment.put(
                Tuple2.of(FunctionDeclarationKind.EQ_ZERO, 1),
                (term, args, model, vars) -> {
                    final Expr<?> op = transform(args.get(0), model, vars);
                    return Eq(op, TypeUtils.getDefaultValue(op.getType()));
                });
        otherFuncs.put(
                Tuple2.of("const", 1),
                (term, args, model, vars) ->
                        transformLit(term, transform(args.get(0), model, vars)));
        otherFuncs.put(
                Tuple2.of("fp", 3),
                (term, args, model, vars) -> {
                    final Expr<BvType> op1 = (Expr<BvType>) transform(args.get(0), model, vars);
                    final Expr<BvType> op2 = (Expr<BvType>) transform(args.get(1), model, vars);
                    final Expr<BvType> op3 = (Expr<BvType>) transform(args.get(2), model, vars);
                    return FpLitExpr.of((BvLitExpr) op1, (BvLitExpr) op2, (BvLitExpr) op3);
                });
    }

    private void addEnvFunc(
            FunctionDeclarationKind declarationKind,
            Tuple2<Integer, QuadFunction<Formula, List<Formula>, Model, List<Decl<?>>, Expr<?>>>
                    func) {
        checkArgument(
                !environment.containsKey(Tuple2.of(declarationKind, func.get1())),
                "Duplicate key: " + Tuple2.of(declarationKind, func.get1()));
        environment.put(Tuple2.of(declarationKind, func.get1()), func.get2());
    }

    private void addOtherFunc(
            String name,
            Tuple2<Integer, QuadFunction<Formula, List<Formula>, Model, List<Decl<?>>, Expr<?>>>
                    func) {
        checkArgument(
                !otherFuncs.containsKey(Tuple2.of(name, func.get1())),
                "Duplicate key: " + Tuple2.of(name, func.get1()));
        otherFuncs.put(Tuple2.of(name, func.get1()), func.get2());
    }

    public Expr<?> toExpr(final Formula term) {
        return transform(term, null, new ArrayList<>());
    }

    ////////

    private Expr<?> transform(final Formula term, final Model model, final List<Decl<?>> vars) {

        try {
            return context.getFormulaManager()
                    .visit(
                            term,
                            new FormulaVisitor<>() {
                                @Override
                                public Expr<?> visitFreeVariable(Formula f, String name) {
                                    return transformVar(f, name, vars);
                                }

                                @Override
                                public Expr<?> visitBoundVariable(Formula f, int deBruijnIdx) {
                                    return Lists.reverse(vars)
                                            .get(deBruijnIdx)
                                            .getRef(); // I think the reverse list is necessary
                                    // here.
                                }

                                @Override
                                public Expr<?> visitConstant(Formula f, Object value) {
                                    return transformLit(f, value);
                                }

                                @Override
                                public Expr<?> visitFunction(
                                        Formula f,
                                        List<Formula> args,
                                        FunctionDeclaration<?> functionDeclaration) {
                                    return transformApp(f, functionDeclaration, args, model, vars);
                                }

                                @Override
                                public Expr<?> visitQuantifier(
                                        BooleanFormula f,
                                        Quantifier quantifier,
                                        List<Formula> boundVariables,
                                        BooleanFormula body) {
                                    return transformQuantifier(
                                            quantifier, boundVariables, model, body, vars);
                                }
                            });
        } catch (JavaSMTSolverException e) {
            throw new JavaSMTSolverException("Not supported: " + term, e);
        }
    }

    private Expr<? extends Type> transformLit(Formula f, Object value) {
        FormulaType<Formula> type = context.getFormulaManager().getFormulaType(f);
        if (type.isIntegerType()) {
            checkArgument(
                    value instanceof BigInteger,
                    "Type mismatch (Expected BigInteger): "
                            + value
                            + " ("
                            + value.getClass().getSimpleName()
                            + ")");
            return transformIntLit(f, (BigInteger) value);
        } else if (type.isRationalType()) {
            checkArgument(
                    value instanceof Rational || value instanceof BigInteger,
                    "Type mismatch (Expected Rational or BigInteger): "
                            + value
                            + " ("
                            + value.getClass().getSimpleName()
                            + ")");
            if (value instanceof Rational) {
                return transformRatLit(f, (Rational) value);
            } else if (value instanceof BigInteger) {
                return transformRatLit(f, (BigInteger) value);
            }
        } else if (type.isBitvectorType()) {
            checkArgument(
                    value instanceof BigInteger,
                    "Type mismatch (Expected BigInteger): "
                            + value
                            + " ("
                            + value.getClass().getSimpleName()
                            + ")");
            return transformBvLit(f, (BigInteger) value);
        } else if (type.isFloatingPointType()) {
            checkArgument(
                    value instanceof FloatingPointNumber,
                    "Type mismatch (Expected FloatingPointNumber): "
                            + value
                            + " ("
                            + value.getClass().getSimpleName()
                            + ")");
            return transformFpLit((FloatingPointNumber) value);
        } else if (type.isArrayType()) {
            checkArgument(
                    value instanceof Expr<?>,
                    "Typ mismatch (Expected Expr): "
                            + value
                            + " ("
                            + value.getClass().getSimpleName()
                            + ")");
            return transformArrLit(f, (Expr<?>) value);
        } else if (type.isBooleanType()) {
            if (Boolean.TRUE.equals(value)) {
                return True();
            } else if (Boolean.FALSE.equals(value)) {
                return False();
            }
        }
        throw new JavaSMTSolverException("Not supported: " + f);
    }

    ////

    private Expr<?> transformIntLit(final Formula term, final BigInteger value) {
        return Int(value);
    }

    private Expr<?> transformRatLit(final Formula term, BigInteger value) {
        return Rat(value, BigInteger.ONE);
    }

    private Expr<?> transformRatLit(final Formula term, Rational value) {
        return Rat(value.getNum(), value.getDen());
    }

    private <T extends Type> Expr<?> transformArrLit(final Formula term, Expr<T> value) {
        final ArrayType<?, T> type =
                (ArrayType<?, T>) transformType(context.getFormulaManager().getFormulaType(term));
        if (value instanceof LitExpr<?>) {
            return ArrayLitExpr.of(List.of(), value, type);
        } else {
            return ArrayInitExpr.of(List.of(), value, type);
        }
    }

    private Expr<?> transformBvLit(final Formula term, BigInteger value) {
        final var bvNum = (BitvectorFormula) term;
        BitvectorType formulaType =
                (BitvectorType) context.getFormulaManager().getFormulaType(bvNum);

        return BvUtils.bigIntegerToNeutralBvLitExpr(value, formulaType.getSize());
    }

    private Expr<?> transformFpLit(FloatingPointNumber value) {
        return FpLitExpr.of(
                value.getSign(),
                BvUtils.bigIntegerToNeutralBvLitExpr(value.getExponent(), value.getExponentSize()),
                BvUtils.bigIntegerToNeutralBvLitExpr(value.getMantissa(), value.getMantissaSize()));
    }

    private Expr<?> transformApp(
            Formula f,
            final FunctionDeclaration<?> funcDecl,
            final List<Formula> args,
            final Model model,
            final List<Decl<?>> vars) {

        final var key1 = Tuple2.of(funcDecl.getKind(), args.size());
        final var key2 = Tuple2.of(funcDecl.getKind(), -1);
        final var key3 = Tuple2.of(funcDecl.getName(), args.size());
        final var key4 = Tuple2.of(funcDecl.getName(), -1);
        if (environment.containsKey(key1)) {
            return environment.get(key1).apply(f, args, model, vars);
        } else if (environment.containsKey(key2)) {
            return environment.get(key2).apply(f, args, model, vars);
        } else if (otherFuncs.containsKey(key3)) {
            return otherFuncs.get(key3).apply(f, args, model, vars);
        } else if (otherFuncs.containsKey(key4)) {
            return otherFuncs.get(key4).apply(f, args, model, vars);
        } else {
            final var paramExprs =
                    args.stream().map((Formula term) -> (Expr) toExpr(term)).toList();

            final Expr<FuncType<Type, Type>> funcExpr;
            if (symbolTable.definesSymbol(funcDecl)) {
                funcExpr =
                        (Expr<FuncType<Type, Type>>)
                                checkNotNull(symbolTable.getConst(funcDecl).getRef());
            } else {
                funcExpr =
                        Const(
                                        funcDecl.getName(),
                                        getFuncType(
                                                transformType(
                                                        context.getFormulaManager()
                                                                .getFormulaType(f)),
                                                args.stream()
                                                        .map(
                                                                context.getFormulaManager()
                                                                        ::getFormulaType)
                                                        .map(this::transformType)
                                                        .toList()))
                                .getRef();
            }

            return FuncExprs.App(funcExpr, paramExprs);
        }
    }

    private <P extends Type, R extends Type> FuncType<P, R> getFuncType(
            final R resultType, final List<P> paramTypes) {
        if (paramTypes.size() == 1) {
            return FuncType.of(paramTypes.get(0), resultType);
        } else {
            return (FuncType<P, R>)
                    FuncType.of(
                            paramTypes.get(0),
                            getFuncType(resultType, paramTypes.subList(1, paramTypes.size())));
        }
    }

    private ParamDecl<?> transformParam(Formula term) {
        final var type = context.getFormulaManager().getFormulaType(term);
        final var thetaType = transformType(type);
        return Param(term.toString(), thetaType);
    }

    private Expr<?> transformQuantifier(
            final Quantifier term,
            final List<Formula> boundVars,
            final Model model,
            final BooleanFormula body,
            final List<Decl<?>> vars) {

        final List<ParamDecl<?>> params =
                boundVars.stream().map(this::transformParam).collect(Collectors.toList());
        final Expr<BoolType> ret;

        pushParams(vars, params);
        final Expr<BoolType> expr = (Expr<BoolType>) transform(body, model, vars);
        popParams(vars, params);

        if (term == Quantifier.EXISTS) {
            ret = Exists(params, expr);
        } else {
            ret = Forall(params, expr);
        }

        return ret;
    }

    private void pushParams(final List<Decl<?>> vars, final List<ParamDecl<?>> paramDecls) {
        vars.addAll(paramDecls);
    }

    private void popParams(final List<Decl<?>> vars, final List<ParamDecl<?>> paramDecls) {
        for (int i = 0; i < paramDecls.size(); i++) {
            vars.remove(vars.size() - 1);
        }
    }

    private Expr<?> transformVar(final Formula term, String name, final List<Decl<?>> vars) {
        FormulaType type = context.getFormulaManager().getFormulaType(term);
        Type thetaType = transformType(type);
        final var c = symbolTable.getConst(term);
        checkState(thetaType == null || c.getType().equals(thetaType));
        return c.getRef();
    }

    private Type transformType(FormulaType type) {
        if (type.isIntegerType()) {
            return Int();
        } else if (type.isRationalType()) {
            return Rat();
        } else if (type.isBitvectorType()) {
            BitvectorType bvType = (BitvectorType) type;
            return BvType.of(bvType.getSize());
        } else if (type.isFloatingPointType()) {
            FloatingPointType fpType = (FloatingPointType) type;
            return FpType.of(fpType.getExponentSize(), fpType.getMantissaSize() + 1);
        } else if (type.isArrayType()) {
            ArrayFormulaType<?, ?> arrayFormulaType = (ArrayFormulaType<?, ?>) type;
            final var indexType = arrayFormulaType.getIndexType();
            final var elemType = arrayFormulaType.getElementType();
            return ArrayType.of(transformType(indexType), transformType(elemType));
        } else if (type.isBooleanType()) {
            return Bool();
        } else if (type.isEnumerationType()) {
            return null;
        }
        throw new JavaSMTSolverException("Type not supported: " + type);
    }

    ////

    private Tuple2<Integer, QuadFunction<Formula, List<Formula>, Model, List<Decl<?>>, Expr<?>>>
            exprNullaryOperator(final Supplier<Expr<?>> function) {
        return Tuple2.of(
                0,
                (term, args, model, vars) -> {
                    checkArgument(args.isEmpty(), "Number of arguments must be zero");
                    return function.get();
                });
    }

    private Tuple2<Integer, QuadFunction<Formula, List<Formula>, Model, List<Decl<?>>, Expr<?>>>
            exprUnaryOperator(final UnaryOperator<Expr<?>> function) {
        return Tuple2.of(
                1,
                (term, args, model, vars) -> {
                    checkArgument(args.size() == 1, "Number of arguments must be one");
                    final Expr<?> op = transform(args.get(0), model, vars);
                    return function.apply(op);
                });
    }

    private Tuple2<Integer, QuadFunction<Formula, List<Formula>, Model, List<Decl<?>>, Expr<?>>>
            exprBinaryOperator(final BinaryOperator<Expr<?>> function) {
        return Tuple2.of(
                2,
                (term, args, model, vars) -> {
                    checkArgument(args.size() == 2, "Number of arguments must be two");
                    if (context.getFormulaManager()
                            .getFormulaType(args.get(0))
                            .isEnumerationType()) {
                        // binary operator is on enum types
                        // if either arg is a literal, we need special handling to get its type
                        int litIndex = -1;
                        for (int i = 0; i < 2; i++) {
                            if (context.getFormulaManager()
                                    .extractVariables(args.get(i))
                                    .isEmpty()) {
                                litIndex = i;
                            }
                        }
                        if (litIndex > -1) {
                            // one is a literal
                            int refIndex = Math.abs(litIndex - 1);
                            final Expr<?> refOp = transform(args.get(refIndex), model, vars);
                            final Expr<EnumType> litExpr =
                                    transformEnumLit(
                                            args.get(litIndex), (EnumType) refOp.getType());
                            return function.apply(refOp, litExpr);
                        }
                    }
                    final Expr<?> op1 = transform(args.get(0), model, vars);
                    final Expr<?> op2 = transform(args.get(1), model, vars);
                    return function.apply(op1, op2);
                });
    }

    private Expr<EnumType> transformEnumLit(Formula formula, EnumType type) {
        return EnumLitExpr.of(type, EnumType.getShortName(formula.toString()));
    }

    private Tuple2<Integer, QuadFunction<Formula, List<Formula>, Model, List<Decl<?>>, Expr<?>>>
            exprTernaryOperator(final TernaryOperator<Expr<?>> function) {
        return Tuple2.of(
                3,
                (term, args, model, vars) -> {
                    checkArgument(args.size() == 3, "Number of arguments must be three");
                    final Expr<?> op1 = transform(args.get(0), model, vars);
                    final Expr<?> op2 = transform(args.get(1), model, vars);
                    final Expr<?> op3 = transform(args.get(2), model, vars);
                    return function.apply(op1, op2, op3);
                });
    }

    private Tuple2<Integer, QuadFunction<Formula, List<Formula>, Model, List<Decl<?>>, Expr<?>>>
            exprMultiaryOperator(final Function<List<Expr<?>>, Expr<?>> function) {
        return Tuple2.of(
                -1,
                (term, args, model, vars) -> {
                    final List<Expr<?>> ops =
                            args.stream()
                                    .map(arg -> transform(arg, model, vars))
                                    .collect(toImmutableList());
                    return function.apply(ops);
                });
    }

    private Tuple2<Integer, QuadFunction<Formula, List<Formula>, Model, List<Decl<?>>, Expr<?>>>
            exprFpUnaryOperator(final BiFunction<FpRoundingMode, Expr<?>, Expr<?>> function) {
        return Tuple2.of(
                2,
                (term, args, model, vars) -> {
                    checkArgument(args.size() == 2, "Number of arguments must be two");
                    final var roundingmode = getRoundingMode(args.get(0).toString());
                    final Expr<?> op2 = transform(args.get(1), model, vars);
                    return function.apply(roundingmode, op2);
                });
    }

    private Tuple2<Integer, QuadFunction<Formula, List<Formula>, Model, List<Decl<?>>, Expr<?>>>
            exprFpBinaryOperator(
                    final TriFunction<FpRoundingMode, Expr<?>, Expr<?>, Expr<?>> function) {
        return Tuple2.of(
                3,
                (term, args, model, vars) -> {
                    checkArgument(args.size() == 3, "Number of arguments must be three");
                    final var roundingmode = getRoundingMode(args.get(0).toString());
                    final Expr<?> op1 = transform(args.get(1), model, vars);
                    final Expr<?> op2 = transform(args.get(2), model, vars);
                    return function.apply(roundingmode, op1, op2);
                });
    }

    private Tuple2<Integer, QuadFunction<Formula, List<Formula>, Model, List<Decl<?>>, Expr<?>>>
            exprFpMultiaryOperator(
                    final BiFunction<FpRoundingMode, List<Expr<?>>, Expr<?>> function) {
        return Tuple2.of(
                -1,
                (term, args, model, vars) -> {
                    final var roundingmode = getRoundingMode(args.get(0).toString());
                    final List<Expr<?>> ops =
                            args.stream()
                                    .skip(1)
                                    .map(arg -> transform(arg, model, vars))
                                    .collect(toImmutableList());
                    return function.apply(roundingmode, ops);
                });
    }

    private Tuple2<Integer, QuadFunction<Formula, List<Formula>, Model, List<Decl<?>>, Expr<?>>>
            exprFpLitUnaryOperator(final BiFunction<BvLitExpr, FpType, Expr<?>> function) {
        return Tuple2.of(
                3,
                (term, args, model, vars) -> {
                    final BvLitExpr op1 = (BvLitExpr) transform(args.get(0), model, vars);
                    final IntLitExpr op2 = (IntLitExpr) transform(args.get(1), model, vars);
                    final IntLitExpr op3 = (IntLitExpr) transform(args.get(2), model, vars);
                    return function.apply(
                            op1,
                            FpType.of(op2.getValue().intValue(), op3.getValue().intValue() + 1));
                });
    }

    private FpRoundingMode getRoundingMode(String s) {
        return switch (s) {
            case "roundNearestTiesToAway" -> FpRoundingMode.RNA;
            case "roundNearestTiesToEven" -> FpRoundingMode.RNE;
            case "roundTowardZero" -> FpRoundingMode.RTZ;
            default -> throw new JavaSMTSolverException("Unexpected value: " + s);
        };
    }
}
