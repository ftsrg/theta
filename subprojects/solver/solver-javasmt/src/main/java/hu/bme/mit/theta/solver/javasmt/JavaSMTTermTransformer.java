/*
 *  Copyright 2024 Budapest University of Technology and Economics
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
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs;
import hu.bme.mit.theta.core.type.arraytype.ArrayInitExpr;
import hu.bme.mit.theta.core.type.arraytype.ArrayLitExpr;
import hu.bme.mit.theta.core.type.arraytype.ArrayType;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.type.bvtype.BvExtractExpr;
import hu.bme.mit.theta.core.type.bvtype.BvLitExpr;
import hu.bme.mit.theta.core.type.bvtype.BvSExtExpr;
import hu.bme.mit.theta.core.type.bvtype.BvType;
import hu.bme.mit.theta.core.type.bvtype.BvZExtExpr;
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
import org.sosy_lab.java_smt.api.Model;
import org.sosy_lab.java_smt.api.QuantifiedFormulaManager.Quantifier;
import org.sosy_lab.java_smt.api.SolverContext;
import org.sosy_lab.java_smt.api.visitors.FormulaVisitor;

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

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;
import static com.google.common.base.Preconditions.checkState;
import static com.google.common.collect.ImmutableList.toImmutableList;
import static hu.bme.mit.theta.core.decl.Decls.Const;
import static hu.bme.mit.theta.core.decl.Decls.Param;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Exists;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.False;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Forall;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.True;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;
import static hu.bme.mit.theta.core.type.rattype.RatExprs.Rat;

final class JavaSMTTermTransformer {

    private static final String PARAM_NAME_FORMAT = "_p%d";

    private final JavaSMTSymbolTable symbolTable;
    private final SolverContext context;
    private final Map<Tuple2<String, Integer>, QuadFunction<Formula, List<Formula>, Model, List<Decl<?>>, Expr<?>>> environment;

    public JavaSMTTermTransformer(final JavaSMTSymbolTable symbolTable, SolverContext context) {
        this.symbolTable = symbolTable;
        this.context = context;

        environment = Containers.createMap();
        addFunc("and", exprMultiaryOperator(hu.bme.mit.theta.core.type.booltype.AndExpr::create));
        addFunc("false", exprNullaryOperator(hu.bme.mit.theta.core.type.booltype.FalseExpr::getInstance));
        addFunc("true", exprNullaryOperator(hu.bme.mit.theta.core.type.booltype.TrueExpr::getInstance));
        addFunc("iff", exprBinaryOperator(hu.bme.mit.theta.core.type.booltype.IffExpr::create));
        addFunc("not", exprUnaryOperator(hu.bme.mit.theta.core.type.booltype.NotExpr::create));
        addFunc("=>", exprBinaryOperator(hu.bme.mit.theta.core.type.booltype.ImplyExpr::create));
        addFunc("xor", exprBinaryOperator(hu.bme.mit.theta.core.type.booltype.XorExpr::create));
        addFunc("or", exprMultiaryOperator(hu.bme.mit.theta.core.type.booltype.OrExpr::create));
        addFunc("ite", exprTernaryOperator(hu.bme.mit.theta.core.type.anytype.IteExpr::create));
        addFunc("if", exprTernaryOperator(hu.bme.mit.theta.core.type.anytype.IteExpr::create));
        addFunc("prime", exprUnaryOperator(hu.bme.mit.theta.core.type.anytype.PrimeExpr::of));
        addFunc("=", exprBinaryOperator(hu.bme.mit.theta.core.type.abstracttype.AbstractExprs::Eq));
        addFunc(">=", exprBinaryOperator(hu.bme.mit.theta.core.type.abstracttype.AbstractExprs::Geq));
        addFunc(">", exprBinaryOperator(hu.bme.mit.theta.core.type.abstracttype.AbstractExprs::Gt));
        addFunc("<=", exprBinaryOperator(hu.bme.mit.theta.core.type.abstracttype.AbstractExprs::Leq));
        addFunc("<", exprBinaryOperator(hu.bme.mit.theta.core.type.abstracttype.AbstractExprs::Lt));
        addFunc("+", exprBinaryOperator(hu.bme.mit.theta.core.type.abstracttype.AbstractExprs::Add));
        addFunc("-", exprBinaryOperator(hu.bme.mit.theta.core.type.abstracttype.AbstractExprs::Sub));
        addFunc("+", exprUnaryOperator(hu.bme.mit.theta.core.type.abstracttype.AbstractExprs::Pos));
        addFunc("-", exprUnaryOperator(hu.bme.mit.theta.core.type.abstracttype.AbstractExprs::Neg));
        addFunc("*", exprBinaryOperator(hu.bme.mit.theta.core.type.abstracttype.AbstractExprs::Mul));
        addFunc("/", exprBinaryOperator(hu.bme.mit.theta.core.type.abstracttype.AbstractExprs::Div));
        addFunc("to_int", exprUnaryOperator(hu.bme.mit.theta.core.type.rattype.RatToIntExpr::create));
        addFunc("div", exprBinaryOperator(hu.bme.mit.theta.core.type.inttype.IntDivExpr::create));
        addFunc("to_rat", exprUnaryOperator(hu.bme.mit.theta.core.type.inttype.IntToRatExpr::create));
        addFunc("mod", exprBinaryOperator(hu.bme.mit.theta.core.type.inttype.IntModExpr::create));
        addFunc("rem", exprBinaryOperator(hu.bme.mit.theta.core.type.inttype.IntRemExpr::create));
        addFunc("fp.add", exprFpMultiaryOperator(hu.bme.mit.theta.core.type.fptype.FpAddExpr::create));
        addFunc("fp.sub", exprFpBinaryOperator(hu.bme.mit.theta.core.type.fptype.FpSubExpr::create));
        addFunc("fp.pos", exprUnaryOperator(hu.bme.mit.theta.core.type.fptype.FpPosExpr::create));
        addFunc("fp.neg", exprUnaryOperator(hu.bme.mit.theta.core.type.fptype.FpNegExpr::create));
        addFunc("fp.mul", exprFpMultiaryOperator(hu.bme.mit.theta.core.type.fptype.FpMulExpr::create));
        addFunc("fp.div", exprFpBinaryOperator(hu.bme.mit.theta.core.type.fptype.FpDivExpr::create));
        addFunc("fp.rem", exprBinaryOperator(hu.bme.mit.theta.core.type.fptype.FpRemExpr::create));
        addFunc("fprem", exprBinaryOperator(hu.bme.mit.theta.core.type.fptype.FpRemExpr::create));
        addFunc("fp.abs", exprUnaryOperator(hu.bme.mit.theta.core.type.fptype.FpAbsExpr::create));
        addFunc("fp.leq", exprBinaryOperator(hu.bme.mit.theta.core.type.fptype.FpLeqExpr::create));
        addFunc("fp.lt", exprBinaryOperator(hu.bme.mit.theta.core.type.fptype.FpLtExpr::create));
        addFunc("fp.geq", exprBinaryOperator(hu.bme.mit.theta.core.type.fptype.FpGeqExpr::create));
        addFunc("fp.gt", exprBinaryOperator(hu.bme.mit.theta.core.type.fptype.FpGtExpr::create));
        addFunc("fp.eq", exprBinaryOperator(hu.bme.mit.theta.core.type.fptype.FpEqExpr::create));
        addFunc("fp.isnan", exprUnaryOperator(hu.bme.mit.theta.core.type.fptype.FpIsNanExpr::create));
        addFunc("fp.isNaN", exprUnaryOperator(hu.bme.mit.theta.core.type.fptype.FpIsNanExpr::create));
        addFunc("isinfinite", exprUnaryOperator(hu.bme.mit.theta.core.type.fptype.FpIsInfiniteExpr::create));
        addFunc("fp.isInfinite", exprUnaryOperator(hu.bme.mit.theta.core.type.fptype.FpIsInfiniteExpr::create));
        addFunc("fp.roundtoint", exprFpUnaryOperator(hu.bme.mit.theta.core.type.fptype.FpRoundToIntegralExpr::create));
        addFunc("fp.roundToIntegral", exprFpUnaryOperator(hu.bme.mit.theta.core.type.fptype.FpRoundToIntegralExpr::create));
        addFunc("fp.sqrt", exprFpUnaryOperator(hu.bme.mit.theta.core.type.fptype.FpSqrtExpr::create));
        addFunc("fp.max", exprBinaryOperator(hu.bme.mit.theta.core.type.fptype.FpMaxExpr::create));
        addFunc("fp.min", exprBinaryOperator(hu.bme.mit.theta.core.type.fptype.FpMinExpr::create));
        addFunc("++", exprMultiaryOperator(hu.bme.mit.theta.core.type.bvtype.BvConcatExpr::create));
        addFunc("concat", exprMultiaryOperator(hu.bme.mit.theta.core.type.bvtype.BvConcatExpr::create));
        addFunc("bvadd", exprMultiaryOperator(hu.bme.mit.theta.core.type.bvtype.BvAddExpr::create));
        addFunc("bvsub", exprBinaryOperator(hu.bme.mit.theta.core.type.bvtype.BvSubExpr::create));
        addFunc("bvpos", exprUnaryOperator(hu.bme.mit.theta.core.type.bvtype.BvPosExpr::create));
        addFunc("bvneg", exprUnaryOperator(hu.bme.mit.theta.core.type.bvtype.BvNegExpr::create));
        addFunc("bvmul", exprMultiaryOperator(hu.bme.mit.theta.core.type.bvtype.BvMulExpr::create));
        addFunc("bvudiv", exprBinaryOperator(hu.bme.mit.theta.core.type.bvtype.BvUDivExpr::create));
        addFunc("bvsdiv", exprBinaryOperator(hu.bme.mit.theta.core.type.bvtype.BvSDivExpr::create));
        addFunc("bvsmod", exprBinaryOperator(hu.bme.mit.theta.core.type.bvtype.BvSModExpr::create));
        addFunc("bvurem", exprBinaryOperator(hu.bme.mit.theta.core.type.bvtype.BvURemExpr::create));
        addFunc("bvsrem", exprBinaryOperator(hu.bme.mit.theta.core.type.bvtype.BvSRemExpr::create));
        addFunc("bvor", exprMultiaryOperator(hu.bme.mit.theta.core.type.bvtype.BvOrExpr::create));
        addFunc("bvand", exprMultiaryOperator(hu.bme.mit.theta.core.type.bvtype.BvAndExpr::create));
        addFunc("bvxor", exprMultiaryOperator(hu.bme.mit.theta.core.type.bvtype.BvXorExpr::create));
        addFunc("bvnot", exprUnaryOperator(hu.bme.mit.theta.core.type.bvtype.BvNotExpr::create));
        addFunc("bvshl", exprBinaryOperator(hu.bme.mit.theta.core.type.bvtype.BvShiftLeftExpr::create));
        addFunc("bvashr", exprBinaryOperator(hu.bme.mit.theta.core.type.bvtype.BvArithShiftRightExpr::create));
        addFunc("bvlshr", exprBinaryOperator(hu.bme.mit.theta.core.type.bvtype.BvLogicShiftRightExpr::create));
        addFunc("bvrol", exprBinaryOperator(hu.bme.mit.theta.core.type.bvtype.BvRotateLeftExpr::create));
        addFunc("ext_rotate_left", exprBinaryOperator(hu.bme.mit.theta.core.type.bvtype.BvRotateLeftExpr::create));
        addFunc("bvror", exprBinaryOperator(hu.bme.mit.theta.core.type.bvtype.BvRotateRightExpr::create));
        addFunc("ext_rotate_right", exprBinaryOperator(hu.bme.mit.theta.core.type.bvtype.BvRotateRightExpr::create));
        addFunc("bvult", exprBinaryOperator(hu.bme.mit.theta.core.type.bvtype.BvULtExpr::create));
        addFunc("bvule", exprBinaryOperator(hu.bme.mit.theta.core.type.bvtype.BvULeqExpr::create));
        addFunc("bvugt", exprBinaryOperator(hu.bme.mit.theta.core.type.bvtype.BvUGtExpr::create));
        addFunc("bvuge", exprBinaryOperator(hu.bme.mit.theta.core.type.bvtype.BvUGeqExpr::create));
        addFunc("bvslt", exprBinaryOperator(hu.bme.mit.theta.core.type.bvtype.BvSLtExpr::create));
        addFunc("bvsle", exprBinaryOperator(hu.bme.mit.theta.core.type.bvtype.BvSLeqExpr::create));
        addFunc("bvsgt", exprBinaryOperator(hu.bme.mit.theta.core.type.bvtype.BvSGtExpr::create));
        addFunc("bvsge", exprBinaryOperator(hu.bme.mit.theta.core.type.bvtype.BvSGeqExpr::create));
        addFunc("read", exprBinaryOperator(hu.bme.mit.theta.core.type.arraytype.ArrayReadExpr::create));
        addFunc("write", exprTernaryOperator(hu.bme.mit.theta.core.type.arraytype.ArrayWriteExpr::create));
        addFunc("select", exprBinaryOperator(hu.bme.mit.theta.core.type.arraytype.ArrayReadExpr::create));
        addFunc("store", exprTernaryOperator(hu.bme.mit.theta.core.type.arraytype.ArrayWriteExpr::create));

        environment.put(Tuple2.of("fp.frombv", 1), (term, args, model, vars) -> {
            FloatingPointType type = (FloatingPointType) context.getFormulaManager().getFormulaType((FloatingPointFormula) term);
            final var roundingmode = getRoundingMode(args.get(0).toString());
            final Expr<BvType> op = (Expr<BvType>) transform(args.get(1), model, vars);
            return FpFromBvExpr.of(roundingmode, op, FpType.of(type.getExponentSize(), type.getMantissaSize() + 1), true);
        });
        environment.put(Tuple2.of("fp.to_sbv", 2), (term, args, model, vars) -> {
            BitvectorType type = (BitvectorType) context.getFormulaManager().getFormulaType((BitvectorFormula) term);
            final var roundingmode = getRoundingMode(args.get(0).toString());
            final Expr<FpType> op = (Expr<FpType>) transform(args.get(1), model, vars);
            return FpToBvExpr.of(roundingmode, op, type.getSize(), true);
        });
        environment.put(Tuple2.of("fp.to_ubv", 2), (term, args, model, vars) -> {
            BitvectorType type = (BitvectorType) context.getFormulaManager().getFormulaType((BitvectorFormula) term);
            final var roundingmode = getRoundingMode(args.get(0).toString());
            final Expr<FpType> op = (Expr<FpType>) transform(args.get(1), model, vars);
            return FpToBvExpr.of(roundingmode, op, type.getSize(), false);
        });
        environment.put(Tuple2.of("to_fp", 2), (term, args, model, vars) -> {
            FloatingPointType type = (FloatingPointType) context.getFormulaManager().getFormulaType((FloatingPointFormula) term);
            final var roundingmode = getRoundingMode(args.get(0).toString());
            final Expr<?> op = transform(args.get(1), model, vars);
            if (op.getType() instanceof FpType) {
                return FpToFpExpr.of(roundingmode, (Expr<FpType>) op, type.getExponentSize(), type.getMantissaSize() + 1);
            } else if (op.getType() instanceof BvType) {
                return FpFromBvExpr.of(roundingmode, (Expr<BvType>) op, FpType.of(type.getExponentSize(), type.getMantissaSize() + 1), false);
            } else {
                throw new JavaSMTSolverException("Unsupported:" + op.getType());
            }
        });
        environment.put(Tuple2.of("to_fp", 1), (term, args, model, vars) -> {
            FloatingPointType type = (FloatingPointType) context.getFormulaManager().getFormulaType((FloatingPointFormula) term);
            final Expr<BvType> op = (Expr<BvType>) transform(args.get(0), model, vars);
            return FpFromBvExpr.of(FpRoundingMode.getDefaultRoundingMode(), op, FpType.of(type.getExponentSize(), type.getMantissaSize() + 1), true);
        });

        environment.put(Tuple2.of("extract", 1), (term, args, model, vars) -> {
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
        environment.put(Tuple2.of("zero_extend", 1), (term, args, model, vars) -> {
            BitvectorType type = (BitvectorType) context.getFormulaManager().getFormulaType((BitvectorFormula) term);
            final Expr<BvType> op = (Expr<BvType>) transform(args.get(0), model, vars);
            return BvZExtExpr.of(op, BvType.of(type.getSize()));
        });
        environment.put(Tuple2.of("sign_extend", 1), (term, args, model, vars) -> {
            BitvectorType type = (BitvectorType) context.getFormulaManager().getFormulaType((BitvectorFormula) term);
            final Expr<BvType> op = (Expr<BvType>) transform(args.get(0), model, vars);
            return BvSExtExpr.of(op, BvType.of(type.getSize()));
        });
        environment.put(Tuple2.of("EqZero", 1), (term, args, model, vars) -> {
            final Expr<?> op = transform(args.get(0), model, vars);
            return AbstractExprs.Eq(op, TypeUtils.getDefaultValue(op.getType()));
        });
        environment.put(Tuple2.of("fp", 3), (term, args, model, vars) -> {
            final Expr<BvType> op1 = (Expr<BvType>) transform(args.get(0), model, vars);
            final Expr<BvType> op2 = (Expr<BvType>) transform(args.get(1), model, vars);
            final Expr<BvType> op3 = (Expr<BvType>) transform(args.get(2), model, vars);
            return FpLitExpr.of((BvLitExpr) op1, (BvLitExpr) op2, (BvLitExpr) op3);
        });
        environment.put(Tuple2.of("const", 1), (term, args, model, vars) -> {
            return transformLit(term, transform(args.get(0), model, vars));
        });
    }

    private void addFunc(String name, Tuple2<Integer, QuadFunction<Formula, List<Formula>, Model, List<Decl<?>>, Expr<?>>> func) {
        checkArgument(!environment.containsKey(Tuple2.of(name, func.get1())), "Duplicate key: " + Tuple2.of(name, func.get1()));
        environment.put(Tuple2.of(name, func.get1()), func.get2());
    }

    public Expr<?> toExpr(final Formula term) {
        return transform(term, null, new ArrayList<>());
    }

    ////////

    private Expr<?> transform(final Formula term, final Model model,
                              final List<Decl<?>> vars) {

        try {
            return context.getFormulaManager().visit(term, new FormulaVisitor<Expr<?>>() {
                @Override
                public Expr<?> visitFreeVariable(Formula f, String name) {
                    return transformVar(f, name, vars);
                }

                @Override
                public Expr<?> visitBoundVariable(Formula f, int deBruijnIdx) {
                    return Lists.reverse(vars).get(deBruijnIdx).getRef(); // I think the reverse list is necessary here.
                }

                @Override
                public Expr<?> visitConstant(Formula f, Object value) {
                    return transformLit(f, value);
                }

                @Override
                public Expr<?> visitFunction(Formula f, List<Formula> args, FunctionDeclaration<?> functionDeclaration) {
                    return transformApp(f, functionDeclaration, args, model, vars);
                }

                @Override
                public Expr<?> visitQuantifier(BooleanFormula f, Quantifier quantifier, List<Formula> boundVariables, BooleanFormula body) {
                    return transformQuantifier(quantifier, boundVariables, model, body, vars);
                }
            });
        } catch (JavaSMTSolverException e) {
            throw new JavaSMTSolverException("Not supported: " + term, e);
        }
    }

    private Expr<? extends Type> transformLit(Formula f, Object value) {
        FormulaType<Formula> type = context.getFormulaManager().getFormulaType(f);
        if (type.isIntegerType()) {
            checkArgument(value instanceof BigInteger, "Type mismatch (Expected BigInteger): " + value + " (" + value.getClass().getSimpleName() + ")");
            return transformIntLit(f, (BigInteger) value);
        } else if (type.isRationalType()) {
            checkArgument(value instanceof Rational || value instanceof BigInteger, "Type mismatch (Expected Rational or BigInteger): " + value + " (" + value.getClass().getSimpleName() + ")");
            if (value instanceof Rational) {
                return transformRatLit(f, (Rational) value);
            } else if (value instanceof BigInteger) {
                return transformRatLit(f, (BigInteger) value);
            }
        } else if (type.isBitvectorType()) {
            checkArgument(value instanceof BigInteger, "Type mismatch (Expected BigInteger): " + value + " (" + value.getClass().getSimpleName() + ")");
            return transformBvLit(f, (BigInteger) value);
        } else if (type.isFloatingPointType()) {
            checkArgument(value instanceof FloatingPointNumber, "Type mismatch (Expected FloatingPointNumber): " + value + " (" + value.getClass().getSimpleName() + ")");
            return transformFpLit((FloatingPointNumber) value);
        } else if (type.isArrayType()) {
            checkArgument(value instanceof Expr<?>, "Typ mismatch (Expected Expr): " + value + " (" + value.getClass().getSimpleName() + ")");
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
        final ArrayType<?, T> type = (ArrayType<?, T>) transformType(context.getFormulaManager().getFormulaType(term));
        if (value instanceof LitExpr<?>) {
            return ArrayLitExpr.of(List.of(), value, type);
        } else {
            return ArrayInitExpr.of(List.of(), value, type);
        }
    }

    private Expr<?> transformBvLit(final Formula term, BigInteger value) {
        final var bvNum = (BitvectorFormula) term;
        BitvectorType formulaType = (BitvectorType) context.getFormulaManager().getFormulaType(bvNum);

        return BvUtils.bigIntegerToNeutralBvLitExpr(value, formulaType.getSize());
    }

    private Expr<?> transformFpLit(FloatingPointNumber value) {
        return FpLitExpr.of(
                value.getSign(),
                BvUtils.bigIntegerToNeutralBvLitExpr(value.getExponent(), value.getExponentSize()),
                BvUtils.bigIntegerToNeutralBvLitExpr(value.getMantissa(), value.getMantissaSize()));
    }

    private Expr<?> transformApp(Formula f, final FunctionDeclaration<?> funcDecl,
                                 final List<Formula> args,
                                 final Model model,
                                 final List<Decl<?>> vars) {

        final var key1 = Tuple2.of(funcDecl.getName(), args.size());
        final var key2 = Tuple2.of(funcDecl.getName(), -1);
        if (environment.containsKey(key1)) {
            return environment.get(key1).apply(f, args, model, vars);
        } else if (environment.containsKey(key2)) {
            return environment.get(key2).apply(f, args, model, vars);
        } else {
            final var paramExprs = args.stream().map((Formula term) -> (Expr) toExpr(term)).toList();

            final Expr<FuncType<Type, Type>> funcExpr;
            if (symbolTable.definesSymbol(funcDecl)) {
                funcExpr = (Expr<FuncType<Type, Type>>) checkNotNull(symbolTable.getConst(funcDecl).getRef());
            } else {
                funcExpr = Const(funcDecl.getName(), getFuncType(
                        transformType(context.getFormulaManager().getFormulaType(f)),
                        args.stream().map(context.getFormulaManager()::getFormulaType).map(this::transformType).toList()
                )).getRef();
            }

            return FuncExprs.App(funcExpr, paramExprs);
        }
    }

    private <P extends Type, R extends Type> FuncType<P, R> getFuncType(final R resultType, final List<P> paramTypes) {
        if (paramTypes.size() == 1) {
            return FuncType.of(paramTypes.get(0), resultType);
        } else {
            return (FuncType<P, R>) FuncType.of(paramTypes.get(0), getFuncType(resultType, paramTypes.subList(1, paramTypes.size())));
        }
    }

    private ParamDecl<?> transformParam(Formula term) {
        final var type = context.getFormulaManager().getFormulaType(term);
        final var thetaType = transformType(type);
        return Param(term.toString(), thetaType);
    }

    private Expr<?> transformQuantifier(final Quantifier term, final List<Formula> boundVars,
                                        final Model model, final BooleanFormula body, final List<Decl<?>> vars) {

        final List<ParamDecl<?>> params = boundVars
                .stream()
                .map(this::transformParam)
                .collect(Collectors.toList());
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
        }
        throw new JavaSMTSolverException("Type not supported: " + type);
    }

    ////

    private Tuple2<Integer, QuadFunction<Formula, List<Formula>, Model, List<Decl<?>>, Expr<?>>> exprNullaryOperator(
            final Supplier<Expr<?>> function) {
        return Tuple2.of(0, (term, args, model, vars) -> {
            checkArgument(args.isEmpty(), "Number of arguments must be zero");
            return function.get();
        });
    }

    private Tuple2<Integer, QuadFunction<Formula, List<Formula>, Model, List<Decl<?>>, Expr<?>>> exprUnaryOperator(
            final UnaryOperator<Expr<?>> function) {
        return Tuple2.of(1, (term, args, model, vars) -> {
            checkArgument(args.size() == 1, "Number of arguments must be one");
            final Expr<?> op = transform(args.get(0), model, vars);
            return function.apply(op);
        });
    }

    private Tuple2<Integer, QuadFunction<Formula, List<Formula>, Model, List<Decl<?>>, Expr<?>>> exprBinaryOperator(
            final BinaryOperator<Expr<?>> function) {
        return Tuple2.of(2, (term, args, model, vars) -> {
            checkArgument(args.size() == 2, "Number of arguments must be two");
            final Expr<?> op1 = transform(args.get(0), model, vars);
            final Expr<?> op2 = transform(args.get(1), model, vars);
            return function.apply(op1, op2);
        });
    }

    private Tuple2<Integer, QuadFunction<Formula, List<Formula>, Model, List<Decl<?>>, Expr<?>>> exprTernaryOperator(
            final TernaryOperator<Expr<?>> function) {
        return Tuple2.of(3, (term, args, model, vars) -> {
            checkArgument(args.size() == 3, "Number of arguments must be three");
            final Expr<?> op1 = transform(args.get(0), model, vars);
            final Expr<?> op2 = transform(args.get(1), model, vars);
            final Expr<?> op3 = transform(args.get(2), model, vars);
            return function.apply(op1, op2, op3);
        });
    }

    private Tuple2<Integer, QuadFunction<Formula, List<Formula>, Model, List<Decl<?>>, Expr<?>>> exprMultiaryOperator(
            final Function<List<Expr<?>>, Expr<?>> function) {
        return Tuple2.of(-1, (term, args, model, vars) -> {
            final List<Expr<?>> ops = args.stream().map(arg -> transform(arg, model, vars))
                    .collect(toImmutableList());
            return function.apply(ops);
        });
    }


    private Tuple2<Integer, QuadFunction<Formula, List<Formula>, Model, List<Decl<?>>, Expr<?>>> exprFpUnaryOperator(
            final BiFunction<FpRoundingMode, Expr<?>, Expr<?>> function) {
        return Tuple2.of(2, (term, args, model, vars) -> {
            checkArgument(args.size() == 2, "Number of arguments must be two");
            final var roundingmode = getRoundingMode(args.get(0).toString());
            final Expr<?> op2 = transform(args.get(1), model, vars);
            return function.apply(roundingmode, op2);
        });
    }

    private Tuple2<Integer, QuadFunction<Formula, List<Formula>, Model, List<Decl<?>>, Expr<?>>> exprFpBinaryOperator(
            final TriFunction<FpRoundingMode, Expr<?>, Expr<?>, Expr<?>> function) {
        return Tuple2.of(3, (term, args, model, vars) -> {
            checkArgument(args.size() == 3, "Number of arguments must be three");
            final var roundingmode = getRoundingMode(args.get(0).toString());
            final Expr<?> op1 = transform(args.get(1), model, vars);
            final Expr<?> op2 = transform(args.get(2), model, vars);
            return function.apply(roundingmode, op1, op2);
        });
    }

    private Tuple2<Integer, QuadFunction<Formula, List<Formula>, Model, List<Decl<?>>, Expr<?>>> exprFpMultiaryOperator(
            final BiFunction<FpRoundingMode, List<Expr<?>>, Expr<?>> function) {
        return Tuple2.of(-1, (term, args, model, vars) -> {
            final var roundingmode = getRoundingMode(args.get(0).toString());
            final List<Expr<?>> ops = args.stream().skip(1).map(arg -> transform(arg, model, vars))
                    .collect(toImmutableList());
            return function.apply(roundingmode, ops);
        });
    }

    private Tuple2<Integer, QuadFunction<Formula, List<Formula>, Model, List<Decl<?>>, Expr<?>>> exprFpLitUnaryOperator(
            final BiFunction<BvLitExpr, FpType, Expr<?>> function) {
        return Tuple2.of(3, (term, args, model, vars) -> {
            final BvLitExpr op1 = (BvLitExpr) transform(args.get(0), model, vars);
            final IntLitExpr op2 = (IntLitExpr) transform(args.get(1), model, vars);
            final IntLitExpr op3 = (IntLitExpr) transform(args.get(2), model, vars);
            return function.apply(op1, FpType.of(op2.getValue().intValue(), op3.getValue().intValue() + 1));
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
 
