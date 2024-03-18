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

import hu.bme.mit.theta.common.TernaryOperator;
import hu.bme.mit.theta.common.TriFunction;
import hu.bme.mit.theta.common.Tuple2;
import hu.bme.mit.theta.common.container.Containers;
import hu.bme.mit.theta.core.decl.Decl;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.bvtype.BvLitExpr;
import hu.bme.mit.theta.core.type.fptype.FpRoundingMode;
import hu.bme.mit.theta.core.type.fptype.FpType;
import hu.bme.mit.theta.core.type.functype.FuncType;
import hu.bme.mit.theta.core.type.inttype.IntLitExpr;
import hu.bme.mit.theta.core.utils.BvUtils;
import org.sosy_lab.common.rationals.Rational;
import org.sosy_lab.java_smt.api.ArrayFormula;
import org.sosy_lab.java_smt.api.BitvectorFormula;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.FloatingPointFormula;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.FormulaType.BitvectorType;
import org.sosy_lab.java_smt.api.FormulaType.FloatingPointType;
import org.sosy_lab.java_smt.api.FunctionDeclaration;
import org.sosy_lab.java_smt.api.Model;
import org.sosy_lab.java_smt.api.QuantifiedFormulaManager.Quantifier;
import org.sosy_lab.java_smt.api.SolverContext;
import org.sosy_lab.java_smt.api.visitors.FormulaVisitor;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Map;
import java.util.StringJoiner;
import java.util.function.BiFunction;
import java.util.function.BinaryOperator;
import java.util.function.Function;
import java.util.function.Supplier;
import java.util.function.UnaryOperator;
import java.util.stream.Collectors;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.collect.ImmutableList.toImmutableList;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.False;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.True;
import static hu.bme.mit.theta.core.type.functype.FuncExprs.App;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;
import static hu.bme.mit.theta.core.type.rattype.RatExprs.Rat;

final class JavaSMTTermTransformer {

    private static final String PARAM_NAME_FORMAT = "_p%d";

    private final JavaSMTSymbolTable symbolTable;
    private final SolverContext context;
    private final Map<Tuple2<String, Integer>, TriFunction<List<Formula>, Model, List<Decl<?>>, Expr<?>>> environment;

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
//        addFunc("fp.frombv", exprFpUnaryOperator(hu.bme.mit.theta.core.type.fptype.FpFromBvExpr::create));
        addFunc("fp.eq", exprBinaryOperator(hu.bme.mit.theta.core.type.fptype.FpEqExpr::create));
        addFunc("fp.isnan", exprUnaryOperator(hu.bme.mit.theta.core.type.fptype.FpIsNanExpr::create));
        addFunc("fp.isNaN", exprUnaryOperator(hu.bme.mit.theta.core.type.fptype.FpIsNanExpr::create));
        addFunc("isinfinite", exprUnaryOperator(hu.bme.mit.theta.core.type.fptype.FpIsInfiniteExpr::create));
        addFunc("fp.roundtoint", exprFpUnaryOperator(hu.bme.mit.theta.core.type.fptype.FpRoundToIntegralExpr::create));
        addFunc("fp.roundToIntegral", exprFpUnaryOperator(hu.bme.mit.theta.core.type.fptype.FpRoundToIntegralExpr::create));
        addFunc("fp.sqrt", exprFpUnaryOperator(hu.bme.mit.theta.core.type.fptype.FpSqrtExpr::create));
        addFunc("fp.max", exprBinaryOperator(hu.bme.mit.theta.core.type.fptype.FpMaxExpr::create));
        addFunc("fp.min", exprBinaryOperator(hu.bme.mit.theta.core.type.fptype.FpMinExpr::create));
//        addFunc("fp.tobv", exprBinaryOperator(hu.bme.mit.theta.core.type.fptype.FpToBvExpr::create));
//        addFunc("fp.tofp", exprUnaryOperator(hu.bme.mit.theta.core.type.fptype.FpToFpExpr::create));
        addFunc("to_fp", exprFpLitUnaryOperator(hu.bme.mit.theta.core.type.fptype.FpLitExpr::of));
        addFunc("++", exprMultiaryOperator(hu.bme.mit.theta.core.type.bvtype.BvConcatExpr::create));
        addFunc("concat", exprMultiaryOperator(hu.bme.mit.theta.core.type.bvtype.BvConcatExpr::create));
//        addFunc("extract", exprTernaryOperator(hu.bme.mit.theta.core.type.bvtype.BvExtractExpr::create));
//        addFunc("bv_zero_extend", exprBinaryOperator(hu.bme.mit.theta.core.type.bvtype.BvZExtExpr::create));
//        addFunc("bv_sign_extend", exprBinaryOperator(hu.bme.mit.theta.core.type.bvtype.BvSExtExpr::create));
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
        addFunc("bvror", exprBinaryOperator(hu.bme.mit.theta.core.type.bvtype.BvRotateRightExpr::create));
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
    }

    private void addFunc(String name, Tuple2<Integer, TriFunction<List<Formula>, Model, List<Decl<?>>, Expr<?>>> func) {
        checkArgument(!environment.containsKey(Tuple2.of(name, func.get1())), "Duplicate key: " + Tuple2.of(name, func.get1()));
        environment.put(Tuple2.of(name, func.get1()), func.get2());
    }

    public Expr<?> toExpr(final Formula term) {
        return transform(term, null, new ArrayList<>());
    }

    public Expr<?> toFuncLitExpr(final FunctionDeclaration<?> funcDecl, final Model model,
                                 final List<Decl<?>> vars) {
        throw new JavaSMTSolverException("Not supported: " + funcDecl);
    }

    private Expr<?> createArrayLitExpr(ArrayFormula<?, ?> sort,
                                       List<Tuple2<List<Expr<?>>, Expr<?>>> entryExprs, Expr<?> elseExpr) {
        throw new JavaSMTSolverException("Not supported: " + sort);
    }

    ////////

    private Expr<?> transform(final Formula term, final Model model,
                              final List<Decl<?>> vars) {

        try {
            return context.getFormulaManager().visit(term, new FormulaVisitor<Expr<?>>() {
                @Override
                public Expr<?> visitFreeVariable(Formula f, String name) {
                    return transformVar(f, vars);
                }

                @Override
                public Expr<?> visitBoundVariable(Formula f, int deBruijnIdx) {
                    return transformVar(f, vars);
                }

                @Override
                public Expr<?> visitConstant(Formula f, Object value) {
                    FormulaType<Formula> type = context.getFormulaManager().getFormulaType(f);
                    if (type.isIntegerType()) {
                        checkArgument(value instanceof BigInteger, "Type mismatch (Expected BigInteger): " + value);
                        return transformIntLit(f, (BigInteger) value);
                    } else if (type.isRationalType()) {
                        checkArgument(value instanceof Rational, "Type mismatch (Expected Rational): " + value);
                        return transformRatLit(f, (Rational) value);
                    } else if (type.isBitvectorType()) {
                        checkArgument(value instanceof BigInteger, "Type mismatch (Expected BigInteger): " + value);
                        return transformBvLit(f, (BigInteger) value);
                    } else if (type.isFloatingPointType()) {
                        checkArgument(value instanceof BigDecimal, "Type mismatch (Expected BigFloat): " + value);
                        return transformFpLit(f, (BigDecimal) value);
                    } else if (type.isArrayType()) {
                        return transformArrLit(f, value, model, vars);
                    } else if (type.isBooleanType()) {
                        if(Boolean.TRUE.equals(value)) {
                            return True();
                        } else if(Boolean.FALSE.equals(value)) {
                            return False();
                        }
                    }
                    throw new JavaSMTSolverException("Not supported: " + f);
                }

                @Override
                public Expr<?> visitFunction(Formula f, List<Formula> args, FunctionDeclaration<?> functionDeclaration) {
                    return transformApp(functionDeclaration, args, model, vars);
                }

                @Override
                public Expr<?> visitQuantifier(BooleanFormula f, Quantifier quantifier, List<Formula> boundVariables, BooleanFormula body) {
                    return transformQuantifier(quantifier, model, vars);
                }
            });
        } catch (JavaSMTSolverException e) {
            throw new JavaSMTSolverException("Not supported: " + term, e);
        }
    }

    ////

    private Expr<?> transformIntLit(final Formula term, final BigInteger value) {
        return Int(value);
    }

    private Expr<?> transformRatLit(final Formula term, Rational value) {
        return Rat(value.getNum(), value.getDen());
    }

    private Expr<?> transformArrLit(final Formula term, Object value, final Model model,
                                    final List<Decl<?>> vars) {
        throw new JavaSMTSolverException("Not supported: " + term);
    }

    private Expr<?> transformBvLit(final Formula term, BigInteger value) {
        final var bvNum = (BitvectorFormula) term;
        BitvectorType formulaType = (BitvectorType) context.getFormulaManager().getFormulaType(bvNum);

        return BvUtils.bigIntegerToNeutralBvLitExpr(value, formulaType.getSize());
    }

    private Expr<?> transformFpLit(final Formula term, BigDecimal value) {
        final var fpNum = (FloatingPointFormula) term;
        FloatingPointType formulaType = (FloatingPointType) context.getFormulaManager().getFormulaType(fpNum);
        FpType type = FpType.of(formulaType.getExponentSize(), formulaType.getMantissaSize());
        throw new JavaSMTSolverException("Not supported: " + value);

//        if (value) {
//            return FpUtils.bigFloatToFpLitExpr(BigFloat.positiveInfinity(type.getSignificand()),
//                    type);
//        } else if (printed.equals("-oo")) {
//            return FpUtils.bigFloatToFpLitExpr(BigFloat.negativeInfinity(type.getSignificand()),
//                    type);
//        } else if (printed.equals("NaN")) {
//            return FpUtils.bigFloatToFpLitExpr(BigFloat.NaN(type.getSignificand()), type);
//        } else if (printed.equals("+zero")) {
//            return FpUtils.bigFloatToFpLitExpr(BigFloat.zero(type.getSignificand()), type);
//        } else if (printed.equals("-zero")) {
//            return FpUtils.bigFloatToFpLitExpr(BigFloat.negativeZero(type.getSignificand()), type);
//        }
//        BigFloat bigFloat = new BigFloat((fpTerm).getSignificand(),
//                FpUtils.getMathContext(type, FpRoundingMode.RNE)).multiply(
//                new BigFloat("2", FpUtils.getMathContext(type, FpRoundingMode.RNE)).pow(
//                        new BigFloat((fpTerm).getExponent(true),
//                                FpUtils.getMathContext(type, FpRoundingMode.RNE)),
//                        FpUtils.getMathContext(type, FpRoundingMode.RNE)),
//                FpUtils.getMathContext(type, FpRoundingMode.RNE));
//        return FpUtils.bigFloatToFpLitExpr(bigFloat, type);
    }

    private Expr<?> transformApp(final FunctionDeclaration<?> funcDecl,
                                 final List<Formula> args,
                                 final Model model,
                                 final List<Decl<?>> vars) {

        final var key1 = Tuple2.of(funcDecl.getName(), args.size());
        final var key2 = Tuple2.of(funcDecl.getName(), -1);
        if(environment.containsKey(key1)) {
            return environment.get(key1).apply(args, model, vars);
        } else if (environment.containsKey(key2)) {
            return environment.get(key2).apply(args, model, vars);
        } else {
            var sj = new StringJoiner(", ", "Not supported: %s(".formatted(funcDecl.getName()), ")");
            args.stream().map(Formula::toString).forEach(sj::add);
            throw new JavaSMTSolverException(sj.toString());
        }
    }

    private Expr<?> transformQuantifier(final Quantifier term, final Model model,
                                        final List<Decl<?>> vars) {
        throw new JavaSMTSolverException("Not supported: " + term);
    }

    private Expr<?> transformVar(final Formula term, final List<Decl<?>> vars) {
        throw new JavaSMTSolverException("Not supported: " + term);
    }

    private <P extends Type, R extends Type> Expr<?> transformFuncApp(final Expr<?> expr,
                                                                      final Formula[] argTerms, final Model model, final List<Decl<?>> vars) {
        final List<Formula> terms = Arrays.stream(argTerms)
                .collect(Collectors.toList());
        return toApp((Expr<FuncType<P, R>>) expr, terms, model, vars);
    }

    private <P extends Type, R extends Type> Expr<?> toApp(Expr<FuncType<P, R>> expr,
                                                           List<Formula> terms, Model model, List<Decl<?>> vars) {
        if (terms.isEmpty()) {
            return expr;
        }
        final Formula term = terms.get(0);
        terms.remove(0);
        final Expr<P> transformed = (Expr<P>) transform(term, model, vars);
        return toApp((Expr<FuncType<FuncType<P, R>, R>>) App(expr, transformed), terms, model,
                vars);
    }

    ////

    private Tuple2<Integer, TriFunction<List<Formula>, Model, List<Decl<?>>, Expr<?>>> exprNullaryOperator(
            final Supplier<Expr<?>> function) {
        return Tuple2.of(0, (args, model, vars) -> {
            checkArgument(args.isEmpty(), "Number of arguments must be zero");
            return function.get();
        });
    }

    private Tuple2<Integer, TriFunction<List<Formula>, Model, List<Decl<?>>, Expr<?>>> exprUnaryOperator(
            final UnaryOperator<Expr<?>> function) {
        return Tuple2.of(1, (args, model, vars) -> {
            checkArgument(args.size() == 1, "Number of arguments must be one");
            final Expr<?> op = transform(args.get(0), model, vars);
            return function.apply(op);
        });
    }

    private Tuple2<Integer, TriFunction<List<Formula>, Model, List<Decl<?>>, Expr<?>>> exprBinaryOperator(
            final BinaryOperator<Expr<?>> function) {
        return Tuple2.of(2, (args, model, vars) -> {
            checkArgument(args.size() == 2, "Number of arguments must be two");
            final Expr<?> op1 = transform(args.get(0), model, vars);
            final Expr<?> op2 = transform(args.get(1), model, vars);
            return function.apply(op1, op2);
        });
    }

    private Tuple2<Integer, TriFunction<List<Formula>, Model, List<Decl<?>>, Expr<?>>> exprTernaryOperator(
            final TernaryOperator<Expr<?>> function) {
        return Tuple2.of(3, (args, model, vars) -> {
            checkArgument(args.size() == 3, "Number of arguments must be three");
            final Expr<?> op1 = transform(args.get(0), model, vars);
            final Expr<?> op2 = transform(args.get(1), model, vars);
            final Expr<?> op3 = transform(args.get(2), model, vars);
            return function.apply(op1, op2, op3);
        });
    }

    private Tuple2<Integer, TriFunction<List<Formula>, Model, List<Decl<?>>, Expr<?>>> exprMultiaryOperator(
            final Function<List<Expr<?>>, Expr<?>> function) {
        return Tuple2.of(-1, (args, model, vars) -> {
            final List<Expr<?>> ops = args.stream().map(arg -> transform(arg, model, vars))
                    .collect(toImmutableList());
            return function.apply(ops);
        });
    }


    private Tuple2<Integer, TriFunction<List<Formula>, Model, List<Decl<?>>, Expr<?>>> exprFpUnaryOperator(
            final BiFunction<FpRoundingMode, Expr<?>, Expr<?>> function) {
        return Tuple2.of(2, (args, model, vars) -> {
            checkArgument(args.size() == 2, "Number of arguments must be two");
            final var roundingmode = getRoundingMode(args.get(0).toString());
            final Expr<?> op2 = transform(args.get(1), model, vars);
            return function.apply(roundingmode, op2);
        });
    }
    
    private Tuple2<Integer, TriFunction<List<Formula>, Model, List<Decl<?>>, Expr<?>>> exprFpBinaryOperator(
            final TriFunction<FpRoundingMode, Expr<?>, Expr<?>, Expr<?>> function) {
        return Tuple2.of(3, (args, model, vars) -> {
            checkArgument(args.size() == 3, "Number of arguments must be three");
            final var roundingmode = getRoundingMode(args.get(0).toString());
            final Expr<?> op1 = transform(args.get(1), model, vars);
            final Expr<?> op2 = transform(args.get(2), model, vars);
            return function.apply(roundingmode, op1, op2);
        });
    }
    
    private Tuple2<Integer, TriFunction<List<Formula>, Model, List<Decl<?>>, Expr<?>>> exprFpMultiaryOperator(
            final BiFunction<FpRoundingMode, List<Expr<?>>, Expr<?>> function) {
        return Tuple2.of(-1, (args, model, vars) -> {
            final var roundingmode = getRoundingMode(args.get(0).toString());
            final List<Expr<?>> ops = args.stream().skip(1).map(arg -> transform(arg, model, vars))
                    .collect(toImmutableList());
            return function.apply(roundingmode, ops);
        });
    }

    private Tuple2<Integer, TriFunction<List<Formula>, Model, List<Decl<?>>, Expr<?>>> exprFpLitUnaryOperator(
        final BiFunction<BvLitExpr, FpType, Expr<?>> function) {
        return Tuple2.of(3, (args, model, vars) -> {
            final BvLitExpr op1 = (BvLitExpr) transform(args.get(0), model, vars);
            final IntLitExpr op2 = (IntLitExpr) transform(args.get(1), model, vars);
            final IntLitExpr op3 = (IntLitExpr) transform(args.get(2), model, vars);
            return function.apply(op1, FpType.of(op2.getValue().intValue(), op3.getValue().intValue()));
        });
    }

    private FpRoundingMode getRoundingMode(String s) {
        return switch (s) {
            case "roundNearestTiesToAway" -> FpRoundingMode.RNA;
            case "roundNearestTiesToEven" -> FpRoundingMode.RNE;
            default -> throw new JavaSMTSolverException("Unexpected value: " + s);
        };
    }


}
 
