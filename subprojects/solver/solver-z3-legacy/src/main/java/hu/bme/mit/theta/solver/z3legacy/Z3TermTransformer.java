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

import static com.google.common.base.Preconditions.*;
import static com.google.common.collect.ImmutableList.toImmutableList;
import static hu.bme.mit.theta.common.Utils.head;
import static hu.bme.mit.theta.common.Utils.tail;
import static hu.bme.mit.theta.core.decl.Decls.Param;
import static hu.bme.mit.theta.core.type.arraytype.ArrayExprs.Array;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.*;
import static hu.bme.mit.theta.core.type.bvtype.BvExprs.BvType;
import static hu.bme.mit.theta.core.type.functype.FuncExprs.App;
import static hu.bme.mit.theta.core.type.functype.FuncExprs.Func;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;
import static hu.bme.mit.theta.core.type.rattype.RatExprs.Rat;
import static java.lang.String.format;

import com.google.common.collect.ImmutableList;
import com.microsoft.z3legacy.*;
import com.microsoft.z3legacy.enumerations.Z3_decl_kind;
import com.microsoft.z3legacy.enumerations.Z3_sort_kind;
import hu.bme.mit.theta.common.TernaryOperator;
import hu.bme.mit.theta.common.TriFunction;
import hu.bme.mit.theta.common.Tuple2;
import hu.bme.mit.theta.common.container.Containers;
import hu.bme.mit.theta.core.decl.Decl;
import hu.bme.mit.theta.core.decl.ParamDecl;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.abstracttype.*;
import hu.bme.mit.theta.core.type.anytype.Exprs;
import hu.bme.mit.theta.core.type.anytype.IteExpr;
import hu.bme.mit.theta.core.type.anytype.PrimeExpr;
import hu.bme.mit.theta.core.type.arraytype.ArrayReadExpr;
import hu.bme.mit.theta.core.type.arraytype.ArrayType;
import hu.bme.mit.theta.core.type.arraytype.ArrayWriteExpr;
import hu.bme.mit.theta.core.type.booltype.*;
import hu.bme.mit.theta.core.type.bvtype.BvAddExpr;
import hu.bme.mit.theta.core.type.bvtype.BvAndExpr;
import hu.bme.mit.theta.core.type.bvtype.BvArithShiftRightExpr;
import hu.bme.mit.theta.core.type.bvtype.BvConcatExpr;
import hu.bme.mit.theta.core.type.bvtype.BvExtractExpr;
import hu.bme.mit.theta.core.type.bvtype.BvLitExpr;
import hu.bme.mit.theta.core.type.bvtype.BvLogicShiftRightExpr;
import hu.bme.mit.theta.core.type.bvtype.BvMulExpr;
import hu.bme.mit.theta.core.type.bvtype.BvNegExpr;
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
import hu.bme.mit.theta.core.type.enumtype.EnumLitExpr;
import hu.bme.mit.theta.core.type.enumtype.EnumType;
import hu.bme.mit.theta.core.type.fptype.FpAbsExpr;
import hu.bme.mit.theta.core.type.fptype.FpAddExpr;
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
import hu.bme.mit.theta.core.type.fptype.FpPosExpr;
import hu.bme.mit.theta.core.type.fptype.FpRemExpr;
import hu.bme.mit.theta.core.type.fptype.FpRoundToIntegralExpr;
import hu.bme.mit.theta.core.type.fptype.FpRoundingMode;
import hu.bme.mit.theta.core.type.fptype.FpSqrtExpr;
import hu.bme.mit.theta.core.type.fptype.FpSubExpr;
import hu.bme.mit.theta.core.type.fptype.FpToBvExpr;
import hu.bme.mit.theta.core.type.fptype.FpToFpExpr;
import hu.bme.mit.theta.core.type.fptype.FpType;
import hu.bme.mit.theta.core.type.functype.FuncType;
import hu.bme.mit.theta.core.type.inttype.IntDivExpr;
import hu.bme.mit.theta.core.type.inttype.IntExprs;
import hu.bme.mit.theta.core.type.inttype.IntLitExpr;
import hu.bme.mit.theta.core.type.inttype.IntModExpr;
import hu.bme.mit.theta.core.type.inttype.IntRemExpr;
import hu.bme.mit.theta.core.type.inttype.IntToRatExpr;
import hu.bme.mit.theta.core.type.inttype.IntType;
import hu.bme.mit.theta.core.type.rattype.RatToIntExpr;
import hu.bme.mit.theta.core.utils.BvUtils;
import hu.bme.mit.theta.core.utils.FpUtils;
import hu.bme.mit.theta.core.utils.TypeUtils;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Arrays;
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
import java.util.stream.Stream;
import org.kframework.mpfr.BigFloat;

final class Z3TermTransformer {

    private static final String PARAM_NAME_FORMAT = "_p%d";

    private final Z3SymbolTable symbolTable;
    private final Map<
                    Tuple2<String, Integer>,
                    TriFunction<com.microsoft.z3legacy.Expr, Model, List<Decl<?>>, Expr<?>>>
            environment;

    public Z3TermTransformer(final Z3SymbolTable symbolTable) {
        this.symbolTable = symbolTable;

        environment = Containers.createMap();

        this.addFunc("deref", dereference());
        this.addFunc("ref", reference());
        this.addFunc("and", this.exprMultiaryOperator(AndExpr::create));
        this.addFunc("false", this.exprNullaryOperator(FalseExpr::getInstance));
        this.addFunc("true", this.exprNullaryOperator(TrueExpr::getInstance));
        this.addFunc("iff", this.exprBinaryOperator(IffExpr::create));
        this.addFunc("not", this.exprUnaryOperator(NotExpr::create));
        this.addFunc("=>", this.exprBinaryOperator(ImplyExpr::create));
        this.addFunc("xor", this.exprBinaryOperator(XorExpr::create));
        this.addFunc("or", this.exprMultiaryOperator(OrExpr::create));
        this.addFunc("ite", this.exprTernaryOperator(IteExpr::create));
        this.addFunc("if", this.exprTernaryOperator(IteExpr::create));
        this.addFunc("prime", this.exprUnaryOperator(PrimeExpr::of));
        this.addFunc("=", this.exprBinaryOperator(AbstractExprs::Eq));
        this.addFunc(">=", this.exprBinaryOperator(AbstractExprs::Geq));
        this.addFunc(">", this.exprBinaryOperator(AbstractExprs::Gt));
        this.addFunc("<=", this.exprBinaryOperator(AbstractExprs::Leq));
        this.addFunc("<", this.exprBinaryOperator(AbstractExprs::Lt));
        this.addFunc("+", this.exprBinaryOperator(AbstractExprs::Add));
        this.addFunc("+", this.exprMultiaryOperator(AbstractExprs::Add));
        this.addFunc("-", this.exprBinaryOperator(AbstractExprs::Sub));
        this.addFunc("+", this.exprUnaryOperator(AbstractExprs::Pos));
        this.addFunc("-", this.exprUnaryOperator(AbstractExprs::Neg));
        this.addFunc("*", this.exprBinaryOperator(AbstractExprs::Mul));
        this.addFunc("*", this.exprMultiaryOperator(AbstractExprs::Mul));
        this.addFunc("/", this.exprBinaryOperator(AbstractExprs::Div));
        this.addFunc("to_real", this.exprUnaryOperator(IntToRatExpr::create));
        this.addFunc("to_int", this.exprUnaryOperator(RatToIntExpr::create));
        this.addFunc("div", this.exprBinaryOperator(IntDivExpr::create));
        this.addFunc("to_rat", this.exprUnaryOperator(IntToRatExpr::create));
        this.addFunc("mod", this.exprBinaryOperator(IntModExpr::create));
        this.addFunc("rem", this.exprBinaryOperator(IntRemExpr::create));
        this.addFunc("fp.add", this.exprFpMultiaryOperator(FpAddExpr::create));
        this.addFunc("fp.sub", this.exprFpBinaryOperator(FpSubExpr::create));
        this.addFunc("fp.pos", this.exprUnaryOperator(FpPosExpr::create));
        this.addFunc("fp.neg", this.exprUnaryOperator(FpNegExpr::create));
        this.addFunc("fp.mul", this.exprFpMultiaryOperator(FpMulExpr::create));
        this.addFunc("fp.div", this.exprFpBinaryOperator(FpDivExpr::create));
        this.addFunc("fp.rem", this.exprBinaryOperator(FpRemExpr::create));
        this.addFunc("fprem", this.exprBinaryOperator(FpRemExpr::create));
        this.addFunc("fp.abs", this.exprUnaryOperator(FpAbsExpr::create));
        this.addFunc("fp.leq", this.exprBinaryOperator(FpLeqExpr::create));
        this.addFunc("fp.lt", this.exprBinaryOperator(FpLtExpr::create));
        this.addFunc("fp.geq", this.exprBinaryOperator(FpGeqExpr::create));
        this.addFunc("fp.gt", this.exprBinaryOperator(FpGtExpr::create));
        this.addFunc("fp.eq", this.exprBinaryOperator(FpEqExpr::create));
        this.addFunc("fp.isnan", this.exprUnaryOperator(FpIsNanExpr::create));
        this.addFunc("fp.isNaN", this.exprUnaryOperator(FpIsNanExpr::create));
        this.addFunc("isinfinite", this.exprUnaryOperator(FpIsInfiniteExpr::create));
        this.addFunc("fp.isInfinite", this.exprUnaryOperator(FpIsInfiniteExpr::create));
        this.addFunc("fp.roundtoint", this.exprFpUnaryOperator(FpRoundToIntegralExpr::create));
        this.addFunc("fp.roundToIntegral", this.exprFpUnaryOperator(FpRoundToIntegralExpr::create));
        this.addFunc("fp.sqrt", this.exprFpUnaryOperator(FpSqrtExpr::create));
        this.addFunc("fp.max", this.exprBinaryOperator(FpMaxExpr::create));
        this.addFunc("fp.min", this.exprBinaryOperator(FpMinExpr::create));
        this.addFunc("++", this.exprMultiaryOperator(BvConcatExpr::create));
        this.addFunc("concat", this.exprMultiaryOperator(BvConcatExpr::create));
        this.addFunc("bvadd", this.exprMultiaryOperator(BvAddExpr::create));
        this.addFunc("bvsub", this.exprBinaryOperator(BvSubExpr::create));
        this.addFunc("bvpos", this.exprUnaryOperator(BvPosExpr::create));
        this.addFunc("bvneg", this.exprUnaryOperator(BvNegExpr::create));
        this.addFunc("bvmul", this.exprMultiaryOperator(BvMulExpr::create));
        this.addFunc("bvudiv", this.exprBinaryOperator(BvUDivExpr::create));
        this.addFunc("bvsdiv", this.exprBinaryOperator(BvSDivExpr::create));
        this.addFunc("bvsmod", this.exprBinaryOperator(BvSModExpr::create));
        this.addFunc("bvurem", this.exprBinaryOperator(BvURemExpr::create));
        this.addFunc("bvsrem", this.exprBinaryOperator(BvSRemExpr::create));
        this.addFunc("bvor", this.exprMultiaryOperator(BvOrExpr::create));
        this.addFunc("bvand", this.exprMultiaryOperator(BvAndExpr::create));
        this.addFunc("bvxor", this.exprMultiaryOperator(BvXorExpr::create));
        this.addFunc("bvnot", this.exprUnaryOperator(BvNotExpr::create));
        this.addFunc("bvshl", this.exprBinaryOperator(BvShiftLeftExpr::create));
        this.addFunc("bvashr", this.exprBinaryOperator(BvArithShiftRightExpr::create));
        this.addFunc("bvlshr", this.exprBinaryOperator(BvLogicShiftRightExpr::create));
        this.addFunc("bvrol", this.exprBinaryOperator(BvRotateLeftExpr::create));
        this.addFunc("ext_rotate_left", this.exprBinaryOperator(BvRotateLeftExpr::create));
        this.addFunc("bvror", this.exprBinaryOperator(BvRotateRightExpr::create));
        this.addFunc("ext_rotate_right", this.exprBinaryOperator(BvRotateRightExpr::create));
        this.addFunc("bvult", this.exprBinaryOperator(BvULtExpr::create));
        this.addFunc("bvule", this.exprBinaryOperator(BvULeqExpr::create));
        this.addFunc("bvugt", this.exprBinaryOperator(BvUGtExpr::create));
        this.addFunc("bvuge", this.exprBinaryOperator(BvUGeqExpr::create));
        this.addFunc("bvslt", this.exprBinaryOperator(BvSLtExpr::create));
        this.addFunc("bvsle", this.exprBinaryOperator(BvSLeqExpr::create));
        this.addFunc("bvsgt", this.exprBinaryOperator(BvSGtExpr::create));
        this.addFunc("bvsge", this.exprBinaryOperator(BvSGeqExpr::create));
        this.addFunc("read", this.exprBinaryOperator(ArrayReadExpr::create));
        this.addFunc("write", this.exprTernaryOperator(ArrayWriteExpr::create));
        this.addFunc("select", this.exprBinaryOperator(ArrayReadExpr::create));
        this.addFunc("store", this.exprTernaryOperator(ArrayWriteExpr::create));
        this.environment.put(
                Tuple2.of("fp.frombv", 1),
                (term, model, vars) -> {
                    FpType type = (FpType) transformSort(term.getSort());
                    FpRoundingMode roundingmode =
                            this.getRoundingMode((term.getArgs()[0]).toString());
                    Expr<BvType> op = (Expr<BvType>) this.transform(term.getArgs()[1], model, vars);
                    return FpFromBvExpr.of(roundingmode, op, type, true);
                });
        this.environment.put(
                Tuple2.of("fp.to_sbv", 2),
                (term, model, vars) -> {
                    BvType type = (BvType) transformSort(term.getSort());
                    FpRoundingMode roundingmode =
                            this.getRoundingMode((term.getArgs()[0]).toString());
                    Expr<FpType> op = (Expr<FpType>) this.transform(term.getArgs()[1], model, vars);
                    return FpToBvExpr.of(roundingmode, op, type.getSize(), true);
                });
        this.environment.put(
                Tuple2.of("fp.to_ubv", 2),
                (term, model, vars) -> {
                    BvType type = (BvType) transformSort(term.getSort());
                    FpRoundingMode roundingmode =
                            this.getRoundingMode((term.getArgs()[0]).toString());
                    Expr<FpType> op = (Expr<FpType>) this.transform(term.getArgs()[1], model, vars);
                    return FpToBvExpr.of(roundingmode, op, type.getSize(), false);
                });
        this.environment.put(
                Tuple2.of("to_fp", 2),
                (term, model, vars) -> {
                    FpType type = (FpType) transformSort(term.getSort());
                    FpRoundingMode roundingmode =
                            this.getRoundingMode((term.getArgs()[0]).toString());
                    Expr<?> op = this.transform(term.getArgs()[1], model, vars);
                    if (op.getType() instanceof FpType) {
                        return FpToFpExpr.of(
                                roundingmode,
                                (Expr<FpType>) op,
                                type.getExponent(),
                                type.getSignificand());
                    } else if (op.getType() instanceof BvType) {
                        return FpFromBvExpr.of(
                                roundingmode,
                                (Expr<BvType>) op,
                                FpType.of(type.getExponent(), type.getSignificand()),
                                false);
                    } else {
                        throw new Z3Exception("Unsupported:" + op.getType());
                    }
                });
        this.environment.put(
                Tuple2.of("to_fp", 1),
                (term, model, vars) -> {
                    FpType type = (FpType) transformSort(term.getSort());
                    Expr<BvType> op = (Expr<BvType>) this.transform(term.getArgs()[0], model, vars);
                    return FpFromBvExpr.of(
                            FpRoundingMode.getDefaultRoundingMode(),
                            op,
                            FpType.of(type.getExponent(), type.getSignificand()),
                            true);
                });
        this.environment.put(
                Tuple2.of("extract", 1),
                (term, model, vars) -> {
                    Pattern pattern = Pattern.compile("extract ([0-9]+) ([0-9]+)");
                    String termStr = term.toString();
                    Matcher match = pattern.matcher(termStr);
                    if (match.find()) {
                        int to = Integer.parseInt(match.group(1)) + 1;
                        int from = Integer.parseInt(match.group(2));
                        Expr<BvType> op =
                                (Expr<BvType>) this.transform(term.getArgs()[0], model, vars);
                        return BvExtractExpr.of(op, IntExprs.Int(from), IntExprs.Int(to));
                    } else {
                        throw new Z3Exception("Not supported: " + term);
                    }
                });
        this.environment.put(
                Tuple2.of("zero_extend", 1),
                (term, model, vars) -> {
                    BvType type = (BvType) transformSort(term.getSort());
                    Expr<BvType> op = (Expr<BvType>) this.transform(term.getArgs()[0], model, vars);
                    return BvZExtExpr.of(op, BvType.of(type.getSize()));
                });
        this.environment.put(
                Tuple2.of("sign_extend", 1),
                (term, model, vars) -> {
                    BvType type = (BvType) transformSort(term.getSort());
                    Expr<BvType> op = (Expr<BvType>) this.transform(term.getArgs()[0], model, vars);
                    return BvSExtExpr.of(op, BvType.of(type.getSize()));
                });
        this.environment.put(
                Tuple2.of("EqZero", 1),
                (term, model, vars) -> {
                    Expr<?> op = this.transform(term.getArgs()[0], model, vars);
                    return AbstractExprs.Eq(op, TypeUtils.getDefaultValue(op.getType()));
                });
        this.environment.put(
                Tuple2.of("fp", 3),
                (term, model, vars) -> {
                    Expr<BvType> op1 =
                            (Expr<BvType>) this.transform(term.getArgs()[0], model, vars);
                    Expr<BvType> op2 =
                            (Expr<BvType>) this.transform(term.getArgs()[1], model, vars);
                    Expr<BvType> op3 =
                            (Expr<BvType>) this.transform(term.getArgs()[2], model, vars);
                    return FpLitExpr.of(
                            ((BvLitExpr) op1).getValue()[0], (BvLitExpr) op2, (BvLitExpr) op3);
                });
        this.environment.put(
                Tuple2.of("const", 1),
                (term, model, vars) -> {
                    return this.transform(term.getArgs()[0], model, vars);
                });
    }

    private void addFunc(
            String name,
            Tuple2<Integer, TriFunction<com.microsoft.z3legacy.Expr, Model, List<Decl<?>>, Expr<?>>>
                    func) {
        assert !environment.containsKey(Tuple2.of(name, func.get1()));
        environment.put(Tuple2.of(name, func.get1()), func.get2());
    }

    public Expr<?> toExpr(final com.microsoft.z3legacy.Expr term) {
        return transform(term, null, new ArrayList<>());
    }

    public Expr<?> toFuncLitExpr(
            final FuncDecl funcDecl, final Model model, final List<Decl<?>> vars) {
        checkNotNull(
                model,
                "Unsupported function '" + funcDecl.getName() + "' in Z3 back-transformation.");
        final com.microsoft.z3legacy.FuncInterp funcInterp = model.getFuncInterp(funcDecl);
        final List<ParamDecl<?>> paramDecls = transformParams(vars, funcDecl.getDomain());
        pushParams(vars, paramDecls);
        final Expr<?> funcLitExpr = transformFuncInterp(funcInterp, model, vars);
        popParams(vars, paramDecls);
        return funcLitExpr;
    }

    public Expr<?> toArrayLitExpr(
            final FuncDecl funcDecl, final Model model, final List<Decl<?>> vars) {
        final com.microsoft.z3legacy.FuncInterp funcInterp = model.getFuncInterp(funcDecl);
        final List<Tuple2<List<Expr<?>>, Expr<?>>> entryExprs =
                createEntryExprs(funcInterp, model, vars);
        final Expr<?> elseExpr = transform(funcInterp.getElse(), model, vars);

        final ArraySort sort = (ArraySort) funcDecl.getRange();

        return createArrayLitExpr(sort, entryExprs, elseExpr);
    }

    private Expr<?> createArrayLitExpr(
            ArraySort sort, List<Tuple2<List<Expr<?>>, Expr<?>>> entryExprs, Expr<?> elseExpr) {
        return this.createIndexValueArrayLitExpr(
                transformSort(sort.getDomain()),
                transformSort(sort.getRange()),
                entryExprs,
                elseExpr);
    }

    @SuppressWarnings("unchecked")
    private <I extends Type, E extends Type> Expr<?> createIndexValueArrayLitExpr(
            I indexType,
            E elemType,
            List<Tuple2<List<Expr<?>>, Expr<?>>> entryExprs,
            Expr<?> elseExpr) {
        return Array(
                entryExprs.stream()
                        .map(
                                entry -> {
                                    checkState(entry.get1().size() == 1);
                                    return Tuple2.of(
                                            (Expr<I>) entry.get1().get(0), (Expr<E>) entry.get2());
                                })
                        .collect(Collectors.toUnmodifiableList()),
                (Expr<E>) elseExpr,
                ArrayType.of(indexType, elemType));
    }

    ////////

    private Expr<?> transform(
            final com.microsoft.z3legacy.Expr term, final Model model, final List<Decl<?>> vars) {
        if (term.isIntNum()) {
            return transformIntLit(term);

        } else if (term.isRatNum()) {
            return transformRatLit(term);

            // BitVecNum is not BVNumeral? Potential bug?
        } else if (
        /* term.isBVNumeral() */ term instanceof com.microsoft.z3legacy.BitVecNum) {
            return transformBvLit(term);

        } else if (term instanceof FPNum) {
            return transformFpLit(term);

        } else if (term.isConstantArray()) {
            return transformArrLit(term, model, vars);

        } else if (term.isApp()) {
            return transformApp(term, model, vars);

        } else if (term.isQuantifier()) {
            final com.microsoft.z3legacy.Quantifier quantifier =
                    (com.microsoft.z3legacy.Quantifier) term;
            return transformQuantifier(quantifier, model, vars);

        } else if (term.isVar()) {
            return transformVar(term, vars);

        } else {
            return transformUnsupported(term, model, vars);
        }
    }

    ////

    private Expr<?> transformIntLit(final com.microsoft.z3legacy.Expr term) {
        final com.microsoft.z3legacy.IntNum intNum = (com.microsoft.z3legacy.IntNum) term;
        try {
            final var value = intNum.getInt64();
            return Int(BigInteger.valueOf(value));
        } catch (Z3Exception ex) {
            final var value = intNum.getBigInteger();
            return Int(value);
        }
    }

    private Expr<?> transformRatLit(final com.microsoft.z3legacy.Expr term) {
        final com.microsoft.z3legacy.RatNum ratNum = (com.microsoft.z3legacy.RatNum) term;
        final var num = ratNum.getNumerator().getBigInteger();
        final var denom = ratNum.getDenominator().getBigInteger();
        return Rat(num, denom);
    }

    private Expr<?> transformArrLit(
            final com.microsoft.z3legacy.Expr term, final Model model, final List<Decl<?>> vars) {
        final ArrayExpr arrayExpr = (ArrayExpr) term;
        final ArraySort sort = (ArraySort) arrayExpr.getSort();
        return createArrayLitExpr(
                sort, Arrays.asList(), transform(arrayExpr.getArgs()[0], model, vars));
    }

    private Expr<?> transformBvLit(final com.microsoft.z3legacy.Expr term) {
        final com.microsoft.z3legacy.BitVecNum bvNum = (com.microsoft.z3legacy.BitVecNum) term;

        BigInteger value = bvNum.getBigInteger();

        return BvUtils.bigIntegerToNeutralBvLitExpr(value, bvNum.getSortSize());
    }

    private Expr<?> transformFpLit(final com.microsoft.z3legacy.Expr term) {
        FPNum fpTerm = (FPNum) term;
        FpType type = FpType.of((fpTerm).getEBits(), (fpTerm).getSBits());
        String printed = term.toString();
        if (printed.equals("+oo")) {
            return FpUtils.bigFloatToFpLitExpr(
                    BigFloat.positiveInfinity(type.getSignificand()), type);
        } else if (printed.equals("-oo")) {
            return FpUtils.bigFloatToFpLitExpr(
                    BigFloat.negativeInfinity(type.getSignificand()), type);
        } else if (printed.equals("NaN")) {
            return FpUtils.bigFloatToFpLitExpr(BigFloat.NaN(type.getSignificand()), type);
        } else if (printed.equals("+zero")) {
            return FpUtils.bigFloatToFpLitExpr(BigFloat.zero(type.getSignificand()), type);
        } else if (printed.equals("-zero")) {
            return FpUtils.bigFloatToFpLitExpr(BigFloat.negativeZero(type.getSignificand()), type);
        }
        BigFloat bigFloat =
                new BigFloat(
                                (fpTerm).getSignificand(),
                                FpUtils.getMathContext(type, FpRoundingMode.RNE))
                        .multiply(
                                new BigFloat("2", FpUtils.getMathContext(type, FpRoundingMode.RNE))
                                        .pow(
                                                new BigFloat(
                                                        (fpTerm).getExponent(),
                                                        FpUtils.getMathContext(
                                                                type, FpRoundingMode.RNE)),
                                                FpUtils.getMathContext(type, FpRoundingMode.RNE)),
                                FpUtils.getMathContext(type, FpRoundingMode.RNE));
        return FpUtils.bigFloatToFpLitExpr(bigFloat, type);
    }

    private Expr<EnumType> transformEnumLit(
            final com.microsoft.z3legacy.Expr term, final EnumType enumType) {
        String longName = term.getFuncDecl().getName().toString();
        String literal = EnumType.getShortName(longName);
        return EnumLitExpr.of(enumType, literal);
    }

    private Expr<?> transformApp(
            final com.microsoft.z3legacy.Expr term, final Model model, final List<Decl<?>> vars) {

        final FuncDecl funcDecl = term.getFuncDecl();
        final String symbol = funcDecl.getName().toString();

        final var key1 = Tuple2.of(symbol, term.getArgs().length);
        final var key2 = Tuple2.of(symbol, -1);
        if (environment.containsKey(key1)) {
            return environment.get(key1).apply(term, model, vars);
        } else if (environment.containsKey(key2)) {
            return environment.get(key2).apply(term, model, vars);
        } else {
            final Expr<?> funcExpr;
            if (symbolTable.definesSymbol(funcDecl)) {
                funcExpr = symbolTable.getConst(funcDecl).getRef();
            } else {
                funcExpr = toFuncLitExpr(funcDecl, model, vars);
            }
            return transformFuncApp(funcExpr, term.getArgs(), model, vars);
        }
    }

    private Expr<?> transformFuncInterp(
            final com.microsoft.z3legacy.FuncInterp funcInterp,
            final Model model,
            final List<Decl<?>> vars) {
        checkArgument(funcInterp.getArity() >= 1);
        final ParamDecl<?> paramDecl = (ParamDecl<?>) vars.get(vars.size() - 1);
        final Expr<?> op =
                createFuncLitExprBody(
                        vars.subList(vars.size() - funcInterp.getArity(), vars.size()).stream()
                                .map(decl -> (ParamDecl<?>) decl)
                                .collect(Collectors.toList()),
                        funcInterp,
                        model,
                        vars);
        return Func(paramDecl, op);
    }

    private Expr<?> createFuncLitExprBody(
            final List<ParamDecl<?>> paramDecl,
            final com.microsoft.z3legacy.FuncInterp funcInterp,
            final Model model,
            final List<Decl<?>> vars) {
        final List<Tuple2<List<Expr<?>>, Expr<?>>> entryExprs =
                createEntryExprs(funcInterp, model, vars);
        final Expr<?> elseExpr = transform(funcInterp.getElse(), model, vars);
        return createNestedIteExpr(paramDecl, entryExprs, elseExpr);
    }

    private Expr<?> createNestedIteExpr(
            final List<ParamDecl<?>> paramDecl,
            final List<Tuple2<List<Expr<?>>, Expr<?>>> entryExprs,
            final Expr<?> elseExpr) {
        if (entryExprs.isEmpty()) {
            return elseExpr;
        } else {
            final Tuple2<List<Expr<?>>, Expr<?>> head = head(entryExprs);
            checkState(
                    paramDecl.size() == head.get1().size(), "Mismatched argument-parameter size!");
            final List<Tuple2<List<Expr<?>>, Expr<?>>> tail = tail(entryExprs);

            Expr<BoolType> cond = null;
            for (int i = 0; i < paramDecl.size(); i++) {
                final Expr<BoolType> newTerm =
                        EqExpr.create2(paramDecl.get(i).getRef(), head.get1().get(i));
                cond = cond == null ? newTerm : And(cond, newTerm);
            }

            final Expr<?> then = head.get2();
            final Expr<?> elze = createNestedIteExpr(paramDecl, tail, elseExpr);
            return IteExpr.create(cond, then, elze);
        }
    }

    private List<Tuple2<List<Expr<?>>, Expr<?>>> createEntryExprs(
            final com.microsoft.z3legacy.FuncInterp funcInterp,
            final Model model,
            final List<Decl<?>> vars) {
        final ImmutableList.Builder<Tuple2<List<Expr<?>>, Expr<?>>> builder =
                ImmutableList.builder();
        for (final com.microsoft.z3legacy.FuncInterp.Entry entry : funcInterp.getEntries()) {
            checkArgument(entry.getArgs().length >= 1);
            final List<Expr<?>> args = new ArrayList<>();
            for (com.microsoft.z3legacy.Expr argTerm : entry.getArgs()) {
                final Expr<?> argExpr = transform(argTerm, model, vars);
                args.add(argExpr);
            }
            final com.microsoft.z3legacy.Expr term2 = entry.getValue();
            final Expr<?> expr2 = transform(term2, model, vars);
            builder.add(Tuple2.of(args, expr2));
        }
        return builder.build();
    }

    private Expr<?> transformQuantifier(
            final com.microsoft.z3legacy.Quantifier term,
            final Model model,
            final List<Decl<?>> vars) {
        if (term.isUniversal()) {
            return transformForall(term, model, vars);

        } else if (term.isExistential()) {
            return transformExists(term, model, vars);

        } else {
            throw new AssertionError("Unhandled case: " + term);
        }
    }

    private Expr<?> transformVar(final com.microsoft.z3legacy.Expr term, final List<Decl<?>> vars) {
        final int index = term.getIndex();
        final Decl<?> decl = vars.get(vars.size() - index - 1);
        return decl.getRef();
    }

    private <P extends Type, R extends Type> Expr<?> transformFuncApp(
            final Expr<?> expr,
            final com.microsoft.z3legacy.Expr[] argTerms,
            final Model model,
            final List<Decl<?>> vars) {
        final List<com.microsoft.z3legacy.Expr> terms =
                Arrays.stream(argTerms).collect(Collectors.toList());
        return toApp((Expr<FuncType<P, R>>) expr, terms, model, vars);
    }

    private <P extends Type, R extends Type> Expr<?> toApp(
            Expr<FuncType<P, R>> expr,
            List<com.microsoft.z3legacy.Expr> terms,
            Model model,
            List<Decl<?>> vars) {
        if (terms.size() == 0) {
            return expr;
        }
        final com.microsoft.z3legacy.Expr term = terms.get(0);
        terms.remove(0);
        final Expr<P> transformed = (Expr<P>) transform(term, model, vars);
        return toApp(
                (Expr<FuncType<FuncType<P, R>, R>>) App(expr, transformed), terms, model, vars);
    }

    ////

    private Expr<?> transformForall(
            final com.microsoft.z3legacy.Expr term, final Model model, final List<Decl<?>> vars) {
        final com.microsoft.z3legacy.Quantifier quantifier =
                (com.microsoft.z3legacy.Quantifier) term;
        final com.microsoft.z3legacy.BoolExpr opTerm = quantifier.getBody();
        final com.microsoft.z3legacy.Sort[] sorts = quantifier.getBoundVariableSorts();
        final List<ParamDecl<?>> paramDecls = transformParams(vars, sorts);

        pushParams(vars, paramDecls);
        final Expr<BoolType> op = TypeUtils.cast(transform(opTerm, model, vars), Bool());
        popParams(vars, paramDecls);

        return Forall(paramDecls, op);
    }

    private Expr<?> transformExists(
            final com.microsoft.z3legacy.Expr term, final Model model, final List<Decl<?>> vars) {
        final com.microsoft.z3legacy.Quantifier quantifier =
                (com.microsoft.z3legacy.Quantifier) term;
        final com.microsoft.z3legacy.BoolExpr opTerm = quantifier.getBody();
        final com.microsoft.z3legacy.Sort[] sorts = quantifier.getBoundVariableSorts();
        final List<ParamDecl<?>> paramDecls = transformParams(vars, sorts);

        pushParams(vars, paramDecls);
        final Expr<BoolType> op = TypeUtils.cast(transform(opTerm, model, vars), Bool());
        popParams(vars, paramDecls);

        return Exists(paramDecls, op);
    }

    private List<ParamDecl<?>> transformParams(
            final List<Decl<?>> vars, final com.microsoft.z3legacy.Sort[] sorts) {
        final ImmutableList.Builder<ParamDecl<?>> builder = ImmutableList.builder();
        for (final com.microsoft.z3legacy.Sort sort : sorts) {
            final ParamDecl<?> param = transformParam(vars, sort);
            builder.add(param);
        }
        final List<ParamDecl<?>> paramDecls = builder.build();
        return paramDecls;
    }

    private ParamDecl<?> transformParam(
            final List<Decl<?>> vars, final com.microsoft.z3legacy.Sort sort) {
        final Type type = transformSort(sort);
        final ParamDecl<?> param = Param(format(PARAM_NAME_FORMAT, vars.size()), type);
        return param;
    }

    private Type transformSort(final com.microsoft.z3legacy.Sort sort) {
        if (sort instanceof com.microsoft.z3legacy.BoolSort) {
            return Bool();
        } else if (sort instanceof com.microsoft.z3legacy.IntSort) {
            return Int();
        } else if (sort instanceof com.microsoft.z3legacy.RealSort) {
            return Rat();
        } else if (sort instanceof com.microsoft.z3legacy.BitVecSort) {
            final com.microsoft.z3legacy.BitVecSort bvSort =
                    (com.microsoft.z3legacy.BitVecSort) sort;
            return BvType(bvSort.getSize());
        } else {
            throw new AssertionError("Unsupported sort: " + sort);
        }
    }

    private void pushParams(final List<Decl<?>> vars, final List<ParamDecl<?>> paramDecls) {
        vars.addAll(paramDecls);
    }

    private void popParams(final List<Decl<?>> vars, final List<ParamDecl<?>> paramDecls) {
        for (int i = 0; i < paramDecls.size(); i++) {
            vars.remove(vars.size() - 1);
        }
    }

    private Expr<?> transformUnsupported(
            final com.microsoft.z3legacy.Expr term, final Model model, final List<Decl<?>> vars) {
        throw new UnsupportedOperationException("Unsupported term: " + term);
    }

    ////

    private Tuple2<Integer, TriFunction<com.microsoft.z3legacy.Expr, Model, List<Decl<?>>, Expr<?>>>
            exprFpUnaryOperator(final BiFunction<FpRoundingMode, Expr<?>, Expr<?>> function) {
        return Tuple2.of(
                2,
                (term, model, vars) -> {
                    checkArgument(term.getArgs().length == 2, "Number of arguments must be two");
                    final var roundingmode = getRoundingMode(term.getArgs()[0].toString());
                    final Expr<?> op2 = transform(term.getArgs()[1], model, vars);
                    return function.apply(roundingmode, op2);
                });
    }

    private Tuple2<Integer, TriFunction<com.microsoft.z3legacy.Expr, Model, List<Decl<?>>, Expr<?>>>
            exprFpBinaryOperator(
                    final TriFunction<FpRoundingMode, Expr<?>, Expr<?>, Expr<?>> function) {
        return Tuple2.of(
                3,
                (term, model, vars) -> {
                    checkArgument(term.getArgs().length == 3, "Number of arguments must be three");
                    final var roundingmode = getRoundingMode(term.getArgs()[0].toString());
                    final Expr<?> op1 = transform(term.getArgs()[1], model, vars);
                    final Expr<?> op2 = transform(term.getArgs()[2], model, vars);
                    return function.apply(roundingmode, op1, op2);
                });
    }

    private Tuple2<Integer, TriFunction<com.microsoft.z3legacy.Expr, Model, List<Decl<?>>, Expr<?>>>
            exprFpMultiaryOperator(
                    final BiFunction<FpRoundingMode, List<Expr<?>>, Expr<?>> function) {
        return Tuple2.of(
                -1,
                (term, model, vars) -> {
                    final var roundingmode = getRoundingMode(term.getArgs()[0].toString());
                    final List<Expr<?>> ops =
                            Arrays.stream(term.getArgs())
                                    .skip(1)
                                    .map(arg -> transform(arg, model, vars))
                                    .collect(toImmutableList());
                    return function.apply(roundingmode, ops);
                });
    }

    private Tuple2<Integer, TriFunction<com.microsoft.z3legacy.Expr, Model, List<Decl<?>>, Expr<?>>>
            exprFpLitUnaryOperator(final BiFunction<BvLitExpr, FpType, Expr<?>> function) {
        return Tuple2.of(
                3,
                (term, model, vars) -> {
                    final BvLitExpr op1 = (BvLitExpr) transform(term.getArgs()[0], model, vars);
                    final IntLitExpr op2 = (IntLitExpr) transform(term.getArgs()[1], model, vars);
                    final IntLitExpr op3 = (IntLitExpr) transform(term.getArgs()[2], model, vars);
                    return function.apply(
                            op1,
                            FpType.of(op2.getValue().intValue(), op3.getValue().intValue() + 1));
                });
    }

    private Tuple2<Integer, TriFunction<com.microsoft.z3legacy.Expr, Model, List<Decl<?>>, Expr<?>>>
            exprNullaryOperator(final Supplier<Expr<?>> function) {
        return Tuple2.of(
                0,
                (term, model, vars) -> {
                    final com.microsoft.z3legacy.Expr[] args = term.getArgs();
                    checkArgument(args.length == 0, "Number of arguments must be zero");
                    return function.get();
                });
    }

    private Tuple2<Integer, TriFunction<com.microsoft.z3legacy.Expr, Model, List<Decl<?>>, Expr<?>>>
            exprUnaryOperator(final UnaryOperator<Expr<?>> function) {
        return Tuple2.of(
                1,
                (term, model, vars) -> {
                    final com.microsoft.z3legacy.Expr[] args = term.getArgs();
                    checkArgument(args.length == 1, "Number of arguments must be one");
                    final Expr<?> op = transform(args[0], model, vars);
                    return function.apply(op);
                });
    }

    private Tuple2<Integer, TriFunction<com.microsoft.z3legacy.Expr, Model, List<Decl<?>>, Expr<?>>>
            exprBinaryOperator(final BinaryOperator<Expr<?>> function) {
        return Tuple2.of(
                2,
                (term, model, vars) -> {
                    final com.microsoft.z3legacy.Expr[] args = term.getArgs();
                    checkArgument(args.length == 2, "Number of arguments must be two");
                    if (args[0].getSort().getSortKind().equals(Z3_sort_kind.Z3_DATATYPE_SORT)) {
                        // binary operator is on enum types
                        // if either arg is a literal, we need special handling to get its type
                        // (references' decl kind is Z3_OP_UNINTERPRETED, literals' decl kind is
                        // Z3_OP_DT_CONSTRUCTOR)
                        int litIndex = -1;
                        for (int i = 0; i < 2; i++) {
                            if (args[i].getFuncDecl()
                                    .getDeclKind()
                                    .equals(Z3_decl_kind.Z3_OP_DT_CONSTRUCTOR)) litIndex = i;
                        }
                        if (litIndex > -1) {
                            int refIndex = Math.abs(litIndex - 1);
                            final Expr<?> refOp = transform(args[refIndex], model, vars);
                            final Expr<EnumType> litExpr =
                                    transformEnumLit(args[litIndex], (EnumType) refOp.getType());
                            return function.apply(refOp, litExpr);
                        }
                    }
                    final Expr<?> op1 = transform(args[0], model, vars);
                    final Expr<?> op2 = transform(args[1], model, vars);
                    return function.apply(op1, op2);
                });
    }

    private Tuple2<Integer, TriFunction<com.microsoft.z3legacy.Expr, Model, List<Decl<?>>, Expr<?>>>
            reference() {
        return Tuple2.of(
                1,
                (term, model, vars) -> {
                    final com.microsoft.z3legacy.Expr[] args = term.getArgs();
                    checkArgument(args.length == 1, "Number of arguments must be one");
                    final Expr<?> op = transform(args[0], model, vars);
                    return Exprs.Reference(op, transformSort(term.getSort()));
                });
    }

    private <T extends Type>
            Tuple2<Integer, TriFunction<com.microsoft.z3legacy.Expr, Model, List<Decl<?>>, Expr<?>>>
                    dereference() {
        return Tuple2.of(
                3,
                (term, model, vars) -> {
                    final com.microsoft.z3legacy.Expr[] args = term.getArgs();
                    checkArgument(args.length == 3, "Number of arguments must be three");
                    final Expr<T> op1 = (Expr<T>) transform(args[0], model, vars);
                    final Expr<T> op2 = (Expr<T>) transform(args[1], model, vars);
                    final Expr<IntType> op3 = (Expr<IntType>) transform(args[2], model, vars);
                    return Exprs.Dereference(op1, op2, transformSort(term.getSort()))
                            .withUniquenessExpr(op3);
                });
    }

    private Tuple2<Integer, TriFunction<com.microsoft.z3legacy.Expr, Model, List<Decl<?>>, Expr<?>>>
            exprTernaryOperator(final TernaryOperator<Expr<?>> function) {
        return Tuple2.of(
                3,
                (term, model, vars) -> {
                    final com.microsoft.z3legacy.Expr[] args = term.getArgs();
                    checkArgument(args.length == 3, "Number of arguments must be three");
                    final Expr<?> op1 = transform(args[0], model, vars);
                    final Expr<?> op2 = transform(args[1], model, vars);
                    final Expr<?> op3 = transform(args[2], model, vars);
                    return function.apply(op1, op2, op3);
                });
    }

    private Tuple2<Integer, TriFunction<com.microsoft.z3legacy.Expr, Model, List<Decl<?>>, Expr<?>>>
            exprMultiaryOperator(final Function<List<Expr<?>>, Expr<?>> function) {
        return Tuple2.of(
                -1,
                (term, model, vars) -> {
                    final com.microsoft.z3legacy.Expr[] args = term.getArgs();
                    final List<Expr<?>> ops =
                            Stream.of(args)
                                    .map(arg -> transform(arg, model, vars))
                                    .collect(toImmutableList());
                    return function.apply(ops);
                });
    }

    private FpRoundingMode getRoundingMode(String s) {
        return switch (s) {
            case "roundNearestTiesToAway" -> FpRoundingMode.RNA;
            case "roundNearestTiesToEven" -> FpRoundingMode.RNE;
            case "roundTowardZero" -> FpRoundingMode.RTZ;
            default -> throw new Z3Exception("Unexpected value: " + s);
        };
    }
}
