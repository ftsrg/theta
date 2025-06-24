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
package hu.bme.mit.theta.solver.smtlib.impl.generic;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.theta.core.decl.Decls.Const;
import static hu.bme.mit.theta.core.decl.Decls.Param;
import static hu.bme.mit.theta.core.type.arraytype.ArrayExprs.Array;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.*;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Exists;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Forall;
import static hu.bme.mit.theta.core.type.functype.FuncExprs.Func;
import static hu.bme.mit.theta.core.type.functype.FuncExprs.UnsafeApp;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;
import static hu.bme.mit.theta.core.type.rattype.RatExprs.Rat;
import static hu.bme.mit.theta.core.utils.TypeUtils.cast;
import static hu.bme.mit.theta.core.utils.TypeUtils.castBv;
import static hu.bme.mit.theta.solver.smtlib.dsl.gen.SMTLIBv2Parser.*;
import static hu.bme.mit.theta.solver.smtlib.dsl.gen.SMTLIBv2Parser.BinaryContext;
import static hu.bme.mit.theta.solver.smtlib.dsl.gen.SMTLIBv2Parser.DecimalContext;
import static hu.bme.mit.theta.solver.smtlib.dsl.gen.SMTLIBv2Parser.Exists_termContext;
import static hu.bme.mit.theta.solver.smtlib.dsl.gen.SMTLIBv2Parser.Forall_termContext;
import static hu.bme.mit.theta.solver.smtlib.dsl.gen.SMTLIBv2Parser.Generic_termContext;
import static hu.bme.mit.theta.solver.smtlib.dsl.gen.SMTLIBv2Parser.HexadecimalContext;
import static hu.bme.mit.theta.solver.smtlib.dsl.gen.SMTLIBv2Parser.IdentifierContext;
import static hu.bme.mit.theta.solver.smtlib.dsl.gen.SMTLIBv2Parser.IndexContext;
import static hu.bme.mit.theta.solver.smtlib.dsl.gen.SMTLIBv2Parser.Let_termContext;
import static hu.bme.mit.theta.solver.smtlib.dsl.gen.SMTLIBv2Parser.NumeralContext;
import static hu.bme.mit.theta.solver.smtlib.dsl.gen.SMTLIBv2Parser.Qual_identifierContext;
import static hu.bme.mit.theta.solver.smtlib.dsl.gen.SMTLIBv2Parser.SortContext;
import static hu.bme.mit.theta.solver.smtlib.dsl.gen.SMTLIBv2Parser.Spec_constantContext;
import static hu.bme.mit.theta.solver.smtlib.dsl.gen.SMTLIBv2Parser.SymbolContext;
import static hu.bme.mit.theta.solver.smtlib.dsl.gen.SMTLIBv2Parser.TermContext;
import static hu.bme.mit.theta.solver.smtlib.impl.generic.GenericSmtLibSymbolTable.encodeSymbol;
import static java.util.stream.Collectors.toList;

import com.google.common.collect.ImmutableList;
import com.google.common.collect.Lists;
import hu.bme.mit.theta.common.QuadFunction;
import hu.bme.mit.theta.common.TernaryOperator;
import hu.bme.mit.theta.common.TriFunction;
import hu.bme.mit.theta.core.decl.ParamDecl;
import hu.bme.mit.theta.core.model.BasicSubstitution;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.abstracttype.*;
import hu.bme.mit.theta.core.type.anytype.IteExpr;
import hu.bme.mit.theta.core.type.arraytype.ArrayReadExpr;
import hu.bme.mit.theta.core.type.arraytype.ArrayType;
import hu.bme.mit.theta.core.type.arraytype.ArrayWriteExpr;
import hu.bme.mit.theta.core.type.booltype.*;
import hu.bme.mit.theta.core.type.bvtype.*;
import hu.bme.mit.theta.core.type.enumtype.EnumType;
import hu.bme.mit.theta.core.type.fptype.*;
import hu.bme.mit.theta.core.type.functype.FuncLitExpr;
import hu.bme.mit.theta.core.type.functype.FuncType;
import hu.bme.mit.theta.core.type.inttype.IntDivExpr;
import hu.bme.mit.theta.core.type.inttype.IntToRatExpr;
import hu.bme.mit.theta.core.type.rattype.RatDivExpr;
import hu.bme.mit.theta.core.type.rattype.RatToIntExpr;
import hu.bme.mit.theta.core.utils.BvUtils;
import hu.bme.mit.theta.core.utils.ExprUtils;
import hu.bme.mit.theta.solver.Stack;
import hu.bme.mit.theta.solver.impl.StackImpl;
import hu.bme.mit.theta.solver.smtlib.dsl.gen.SMTLIBv2Lexer;
import hu.bme.mit.theta.solver.smtlib.dsl.gen.SMTLIBv2Parser;
import hu.bme.mit.theta.solver.smtlib.solver.SmtLibEnumStrategy;
import hu.bme.mit.theta.solver.smtlib.solver.SmtLibSolverException;
import hu.bme.mit.theta.solver.smtlib.solver.model.SmtLibModel;
import hu.bme.mit.theta.solver.smtlib.solver.parser.ThrowExceptionErrorListener;
import hu.bme.mit.theta.solver.smtlib.solver.transformer.SmtLibSymbolTable;
import hu.bme.mit.theta.solver.smtlib.solver.transformer.SmtLibTermTransformer;
import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.*;
import java.util.function.*;
import java.util.stream.Collectors;
import kotlin.Pair;
import org.antlr.v4.runtime.CharStreams;
import org.antlr.v4.runtime.CommonTokenStream;

public class GenericSmtLibTermTransformer implements SmtLibTermTransformer {

    protected final SmtLibSymbolTable symbolTable;
    protected final Map<String, OperatorCreatorFunction> funAppTransformer;
    protected final SmtLibEnumStrategy enumStrategy;

    public GenericSmtLibTermTransformer(final SmtLibSymbolTable symbolTable) {
        this(symbolTable, SmtLibEnumStrategy.getDefaultStrategy());
    }

    public GenericSmtLibTermTransformer(
            final SmtLibSymbolTable symbolTable, final SmtLibEnumStrategy enumStrategy) {
        this.symbolTable = symbolTable;
        this.enumStrategy = enumStrategy;
        this.funAppTransformer =
                new HashMap<>() {
                    {
                        // Generic
                        put("ite", exprIteOperator());

                        // Abstract
                        put("=", exprRelationalOperator(EqExpr::create2));
                        put("<=", exprRelationalOperator(LeqExpr::create2));
                        put("<", exprRelationalOperator(LtExpr::create2));
                        put(">=", exprRelationalOperator(GeqExpr::create2));
                        put(">", exprRelationalOperator(GtExpr::create2));
                        put("+", exprMultiaryOperator(AddExpr::create2));
                        put("-", exprMinusOperator());
                        put("*", exprMultiaryOperator(MulExpr::create2));
                        put("div", exprBinaryOperator(IntDivExpr::create));
                        put("/", exprBinaryOperator(RatDivExpr::create));
                        put("mod", exprBinaryOperator(ModExpr::create2));
                        put("rem", exprBinaryOperator(RemExpr::create2));

                        // Booleal
                        put("not", exprUnaryOperator(NotExpr::create));
                        put("or", exprMultiaryOperator(OrExpr::create));
                        put("and", exprMultiaryOperator(AndExpr::create));
                        put("xor", exprBinaryOperator(XorExpr::create));
                        put("iff", exprBinaryOperator(IffExpr::create));
                        put("=>", exprBinaryOperator(ImplyExpr::create));

                        // Integer
                        put("to_real", exprUnaryOperator(IntToRatExpr::create));

                        // Rational
                        put("to_int", exprUnaryOperator(RatToIntExpr::create));

                        // Bitvector
                        put("concat", exprMultiaryOperator(BvConcatExpr::create));
                        put("extract", exprBvExtractOperator());
                        put("zero_extend", exprBvExtendOperator(BvZExtExpr::create));
                        put("sign_extend", exprBvExtendOperator(BvSExtExpr::create));
                        put("bvadd", exprMultiaryOperator(BvAddExpr::create));
                        put("bvsub", exprBinaryOperator(BvSubExpr::create));
                        put("bvneg", exprUnaryOperator(BvNegExpr::create));
                        put("bvmul", exprMultiaryOperator(BvAddExpr::create));
                        put("bvudiv", exprBinaryOperator(BvUDivExpr::create));
                        put("bvsdiv", exprBinaryOperator(BvSDivExpr::create));
                        put("bvsmod", exprBinaryOperator(BvSModExpr::create));
                        put("bvsrem", exprBinaryOperator(BvURemExpr::create));
                        put("bvurem", exprBinaryOperator(BvSRemExpr::create));
                        put("bvand", exprMultiaryOperator(BvAndExpr::create));
                        put("bvor", exprMultiaryOperator(BvOrExpr::create));
                        put("bvxor", exprMultiaryOperator(BvXorExpr::create));
                        put("bvnot", exprUnaryOperator(BvNotExpr::create));
                        put("bvshl", exprBinaryOperator(BvShiftLeftExpr::create));
                        put("bvashr", exprBinaryOperator(BvArithShiftRightExpr::create));
                        put("bvlshr", exprBinaryOperator(BvLogicShiftRightExpr::create));
                        put("bvult", exprBinaryOperator(BvULtExpr::create));
                        put("bvslt", exprBinaryOperator(BvSLtExpr::create));
                        put("bvule", exprBinaryOperator(BvULeqExpr::create));
                        put("bvsle", exprBinaryOperator(BvSLeqExpr::create));
                        put("bvugt", exprBinaryOperator(BvUGtExpr::create));
                        put("bvsgt", exprBinaryOperator(BvSGtExpr::create));
                        put("bvuge", exprBinaryOperator(BvUGeqExpr::create));
                        put("bvsge", exprBinaryOperator(BvSGeqExpr::create));

                        // Floating point

                        put("fp", exprFpLit());
                        put("fp.add", exprFpMultiaryOperator(FpAddExpr::create));
                        put("fp.sub", exprFpBinaryOperator(FpSubExpr::create));
                        put("fp.neg", exprUnaryOperator(FpNegExpr::create));
                        put("fp.mul", exprFpMultiaryOperator(FpMulExpr::create));
                        put("fp.div", exprFpBinaryOperator(FpDivExpr::create));
                        put("fp.eq", exprBinaryOperator(FpEqExpr::create));
                        put("fp.geq", exprBinaryOperator(FpGeqExpr::create));
                        put("fp.gt", exprBinaryOperator(FpGtExpr::create));
                        put("fp.leq", exprBinaryOperator(FpLeqExpr::create));
                        put("fp.lt", exprBinaryOperator(FpLtExpr::create));
                        put("fp.abs", exprUnaryOperator(FpAbsExpr::create));
                        put(
                                "fp.roundToIntegral",
                                exprFpUnaryOperator(FpRoundToIntegralExpr::create));
                        put("fp.min", exprBinaryOperator(FpMinExpr::create));
                        put("fp.max", exprBinaryOperator(FpMaxExpr::create));
                        put("fp.sqrt", exprFpUnaryOperator(FpSqrtExpr::create));
                        put("fp.rem", exprBinaryOperator(FpRemExpr::create));
                        put("fp.isNaN", exprUnaryOperator(FpIsNanExpr::create));

                        // Array
                        put("select", exprArrayReadOperator());
                        put("store", exprArrayWriteOperator());

                        // Proof
                        put("hyper-res", expectedFunc("hyper-res"));
                        put("asserted", expectedFunc("asserted"));
                        put("mp", expectedFunc("mp"));
                    }
                };
    }

    /* Public interface */

    @Override
    public <P extends Type, R extends Type> LitExpr<FuncType<P, R>> toFuncLitExpr(
            final String funcLitImpl, final FuncType<P, R> type, final SmtLibModel model) {
        final var litExpr = toFuncLitExpr(funcLitImpl, model);
        if (litExpr == null) {
            return null;
        } else if (litExpr instanceof LitExpr) {
            return (LitExpr<FuncType<P, R>>) cast(litExpr, type);
        } else {
            return (LitExpr<FuncType<P, R>>) cast(ExprUtils.simplify(litExpr), type);
        }
    }

    private Expr<?> toFuncLitExpr(final String funcLitImpl, final SmtLibModel model) {
        final var lexer = new SMTLIBv2Lexer(CharStreams.fromString(funcLitImpl));
        final var parser = new SMTLIBv2Parser(new CommonTokenStream(lexer));
        lexer.removeErrorListeners();
        lexer.addErrorListener(new ThrowExceptionErrorListener());
        parser.removeErrorListeners();
        parser.addErrorListener(new ThrowExceptionErrorListener());

        return transformFuncDef(parser.function_def(), model, new StackImpl<>());
    }

    @Override
    public <T extends Type> Expr<T> toExpr(
            final String term, final T type, final SmtLibModel model) {
        final var expr = toExpr(term, model);
        return cast(expr, type);
    }

    private Expr<?> toExpr(final String term, final SmtLibModel model) {
        final var lexer = new SMTLIBv2Lexer(CharStreams.fromString(term));
        final var parser = new SMTLIBv2Parser(new CommonTokenStream(lexer));
        lexer.removeErrorListeners();
        lexer.addErrorListener(new ThrowExceptionErrorListener());
        parser.removeErrorListeners();
        parser.addErrorListener(new ThrowExceptionErrorListener());

        return transformTerm(parser.term(), model, new StackImpl<>());
    }

    @Override
    public <T extends Type> LitExpr<T> toLitExpr(
            final String litImpl, final T type, final SmtLibModel model) {
        if (type instanceof EnumType enumType)
            return (LitExpr<T>) cast(toEnumLitExpr(litImpl, enumType, model), type);
        final var litExpr = toLitExpr(litImpl, model);

        if (litExpr == null) {
            return null;
        } else if (litExpr instanceof LitExpr) {
            return (LitExpr<T>) cast(litExpr, type);
        } else {
            return (LitExpr<T>) cast(ExprUtils.simplify(litExpr), type);
        }
    }

    private Expr<?> toLitExpr(final String litImpl, final SmtLibModel model) {
        final var lexer = new SMTLIBv2Lexer(CharStreams.fromString(litImpl));
        final var parser = new SMTLIBv2Parser(new CommonTokenStream(lexer));
        lexer.removeErrorListeners();
        lexer.addErrorListener(new ThrowExceptionErrorListener());
        parser.removeErrorListeners();
        parser.addErrorListener(new ThrowExceptionErrorListener());

        final var funcDef = parser.function_def();
        final List<ParamDecl<? extends Type>> paramDecls =
                funcDef.sorted_var().stream()
                        .map(sv -> Param(getSymbol(sv.symbol()), transformSort(sv.sort())))
                        .collect(toList());

        final var vars = new StackImpl<ParamDecl<?>>();
        pushParams(paramDecls, vars);
        final var expr = transformTerm(funcDef.term(), model, vars);
        popParams(paramDecls, vars);

        return expr;
    }

    private LitExpr<EnumType> toEnumLitExpr(
            final String litImpl, final EnumType type, final SmtLibModel model) {
        final var lexer = new SMTLIBv2Lexer(CharStreams.fromString(litImpl));
        final var parser = new SMTLIBv2Parser(new CommonTokenStream(lexer));
        lexer.removeErrorListeners();
        lexer.addErrorListener(new ThrowExceptionErrorListener());
        parser.removeErrorListeners();
        parser.addErrorListener(new ThrowExceptionErrorListener());

        final var funcDef = parser.function_def();
        return enumStrategy.transformEnumTerm(funcDef, type, model);
    }

    @Override
    @SuppressWarnings("unchecked")
    public <I extends Type, E extends Type> LitExpr<ArrayType<I, E>> toArrayLitExpr(
            final String arrayLitImpl, final ArrayType<I, E> type, final SmtLibModel model) {
        final var arrayLitExpr = toLitExpr(arrayLitImpl, model);

        if (arrayLitExpr == null) {
            return null;
        } else if (arrayLitExpr instanceof IteExpr) {
            final var entryExprsBuilder =
                    new ImmutableList.Builder<Pair<? extends Expr<I>, ? extends Expr<E>>>();
            var iteExpr = (IteExpr<E>) arrayLitExpr;
            while (true) {
                entryExprsBuilder.add(
                        new Pair<>((Expr<I>) iteExpr.getCond().getOps().get(1), iteExpr.getThen()));
                if (iteExpr.getElse() instanceof IteExpr) {
                    iteExpr = (IteExpr<E>) iteExpr.getElse();
                } else {
                    return Array(entryExprsBuilder.build(), iteExpr.getElse(), type);
                }
            }
        } else {
            return (LitExpr<ArrayType<I, E>>) cast(ExprUtils.simplify(arrayLitExpr), type);
        }
    }

    @Override
    public LitExpr<BvType> toBvLitExpr(
            final String bvLitImpl, final BvType type, final SmtLibModel model) {
        final var bvLitExpr = toLitExpr(bvLitImpl, model);

        if (bvLitExpr == null) {
            return null;
        } else if (bvLitExpr instanceof BvLitExpr) {
            return (BvLitExpr) bvLitExpr;
        } else {
            return (LitExpr<BvType>) cast(ExprUtils.simplify(bvLitExpr), type);
        }
    }

    /* End of public interface */

    /* Visitor implementation */

    protected Expr<?> transformFuncDef(
            final SMTLIBv2Parser.Function_defContext ctx,
            final SmtLibModel model,
            final Stack<ParamDecl<?>> vars) {
        assert model != null;
        assert vars != null;

        final List<ParamDecl<? extends Type>> paramDecls =
                ctx.sorted_var().stream()
                        .map(
                                sv ->
                                        Param(
                                                encodeSymbol(getSymbol(sv.symbol())),
                                                transformSort(sv.sort())))
                        .collect(toList());

        pushParams(paramDecls, vars);
        var op = transformTerm(ctx.term(), model, vars);
        popParams(paramDecls, vars);
        for (ParamDecl<?> param : Lists.reverse(paramDecls)) {
            op = Func(param, op);
        }
        return op;
    }

    protected Expr<?> transformTerm(
            final TermContext ctx, final SmtLibModel model, final Stack<ParamDecl<?>> vars) {
        assert model != null;
        assert vars != null;

        if (ctx.spec_constant() != null) {
            return transformSpecConstant(ctx.spec_constant(), model, vars);
        } else if (ctx.qual_identifier() != null) {
            return transformQualIdentifier(ctx.qual_identifier(), model, vars);
        } else if (ctx.generic_term() != null) {
            return transformGenericTerm(ctx.generic_term(), model, vars);
        } else if (ctx.let_term() != null) {
            return transformLetTerm(ctx.let_term(), model, vars);
        } else if (ctx.forall_term() != null) {
            return transformForallTerm(ctx.forall_term(), model, vars);
        } else if (ctx.exists_term() != null) {
            return transformExistsTerm(ctx.exists_term(), model, vars);
        } else if (ctx.match_term() != null) {
            throw new SmtLibSolverException("");
        } else if (ctx.annotate_term() != null) {
            return transformTerm(ctx.annotate_term().term(), model, vars);
        } else {
            throw new SmtLibSolverException("Invalid input");
        }
    }

    protected Expr<?> transformSpecConstant(
            final Spec_constantContext ctx,
            final SmtLibModel model,
            final Stack<ParamDecl<?>> vars) {
        assert model != null;
        assert vars != null;

        if (ctx.numeral() != null) {
            return transformNumeral(ctx.numeral(), model, vars);
        } else if (ctx.decimal() != null) {
            return transformDecimal(ctx.decimal(), model, vars);
        } else if (ctx.hexadecimal() != null) {
            return transformHexadecimal(ctx.hexadecimal(), model, vars);
        } else if (ctx.binary() != null) {
            return transformBinary(ctx.binary(), model, vars);
        } else if (ctx.string() != null) {
            throw new SmtLibSolverException("");
        } else {
            throw new SmtLibSolverException("Invalid input");
        }
    }

    protected Expr<?> transformQualIdentifier(
            final Qual_identifierContext ctx,
            final SmtLibModel model,
            final Stack<ParamDecl<?>> vars) {
        assert model != null;
        assert vars != null;

        return transformIdentifier(ctx.identifier(), model, vars);
    }

    protected Expr<?> transformGenericTerm(
            final Generic_termContext ctx,
            final SmtLibModel model,
            final Stack<ParamDecl<?>> vars) {
        assert model != null;
        assert vars != null;

        final var funName = getSymbol(ctx.qual_identifier().identifier().symbol());

        final var funParams = ctx.qual_identifier().identifier().index();
        final var funAppParams = ctx.term();

        if (funName.equals("const")) { // as const construct
            final var constType = transformSort(ctx.qual_identifier().sort());
            if (constType instanceof ArrayType) {
                checkArgument(funAppParams.size() == 1, "Invalid as const construct");

                final var arrayType = (ArrayType<?, ?>) constType;
                final var expr = transformTerm(funAppParams.get(0), model, vars);
                return createArrayLitExpr(expr, arrayType);
            } else {
                throw new SmtLibSolverException("");
            }
        } else if (funAppTransformer.containsKey(funName)) { // known function application
            return funAppTransformer.get(funName).apply(funParams, funAppParams, model, vars);
        } else { // custom function application
            //            checkArgument(funParams.size() == 0,
            //                    "Custom unary function application cannot have parameter");
            //            checkArgument(funAppParams.size() == 1, "Only unary functions are
            // supported");

            return createFuncAppExpr(funName, funAppParams, model, vars);
        }
    }

    @SuppressWarnings("unchecked")
    private <I extends Type, E extends Type> Expr<?> createArrayLitExpr(
            final Expr<?> elze, final ArrayType<I, E> type) {
        return Array(Collections.emptyList(), (Expr<E>) elze, type);
    }

    private <P extends Type, R extends Type> Expr<?> createFuncAppExpr(
            final String funName,
            final List<TermContext> funAppParams,
            final SmtLibModel model,
            final Stack<ParamDecl<?>> vars) {
        final Expr<?> funcExpr;
        if (symbolTable.definesSymbol(funName)) {
            funcExpr = checkNotNull(symbolTable.getConst(funName).getRef());
        } else {
            final var funDefImpl = model.getTerm(funName);
            if (funDefImpl == null) {
                throw new SmtLibSolverException(
                        "Model (%s) does not have function \"%s\".".formatted(model, funName));
            }
            funcExpr = toFuncLitExpr(funDefImpl, model);
        }

        final List<Expr<?>> params =
                funAppParams.stream()
                        .map(it -> (Expr<?>) transformTerm(it, model, vars))
                        .collect(Collectors.toUnmodifiableList());
        return UnsafeApp(funcExpr, params);
    }

    protected Expr<?> transformLetTerm(
            final Let_termContext ctx, final SmtLibModel model, final Stack<ParamDecl<?>> vars) {
        assert model != null;
        assert vars != null;

        final var paramDecls = new ArrayList<ParamDecl<? extends Type>>();
        final var paramDefs = new ArrayList<Expr<? extends Type>>();
        for (final var bnd : ctx.var_binding()) {
            final var def = transformTerm(bnd.term(), model, vars);
            final var decl = Param(getSymbol(bnd.symbol()), def.getType());

            paramDecls.add(decl);
            paramDefs.add(def);
        }

        pushParams(paramDecls, vars);
        final var term = transformTerm(ctx.term(), model, vars);
        popParams(paramDecls, vars);

        final var substitutionBuilder = BasicSubstitution.builder();
        for (var i = 0; i < paramDecls.size(); i++) {
            substitutionBuilder.put(paramDecls.get(i), paramDefs.get(i));
        }

        return substitutionBuilder.build().apply(term);
    }

    protected Expr<?> transformForallTerm(
            final Forall_termContext ctx, final SmtLibModel model, final Stack<ParamDecl<?>> vars) {
        assert model != null;
        assert vars != null;

        final List<ParamDecl<? extends Type>> paramDecls =
                ctx.sorted_var().stream()
                        .map(sv -> Param(getSymbol(sv.symbol()), transformSort(sv.sort())))
                        .collect(toList());

        pushParams(paramDecls, vars);
        final var op = transformTerm(ctx.term(), model, vars);
        popParams(paramDecls, vars);

        assert op != null;
        return Forall(paramDecls, cast(op, Bool()));
    }

    protected Expr<?> transformExistsTerm(
            final Exists_termContext ctx, final SmtLibModel model, final Stack<ParamDecl<?>> vars) {
        assert model != null;
        assert vars != null;

        final List<ParamDecl<? extends Type>> paramDecls =
                ctx.sorted_var().stream()
                        .map(sv -> Param(getSymbol(sv.symbol()), transformSort(sv.sort())))
                        .collect(toList());

        pushParams(paramDecls, vars);
        final var op = transformTerm(ctx.term(), model, vars);
        popParams(paramDecls, vars);

        assert op != null;
        return Exists(paramDecls, cast(op, Bool()));
    }

    protected Expr<?> transformIdentifier(
            final IdentifierContext ctx, final SmtLibModel model, final Stack<ParamDecl<?>> vars) {
        assert model != null;
        assert vars != null;

        if (getSymbol(ctx.symbol()).equals("as-array")) {
            final var name = ctx.index().get(0).getText();
            final var funcLit = (FuncLitExpr<?, ?>) toFuncLitExpr(model.getTerm(name), model);
            return funcLit.getResult();
        } else if (getSymbol(ctx.symbol()).startsWith("bv")) {
            final var value = getSymbol(ctx.symbol()).substring(2);
            final var bvSize = Integer.parseInt(ctx.index().get(0).getText());
            return BvUtils.bigIntegerToNeutralBvLitExpr(new BigInteger(value), bvSize);
        } else if (getSymbol(ctx.symbol()).equals("+oo")) {
            final var eb = Integer.parseInt(ctx.index().get(0).getText());
            final var sb = Integer.parseInt(ctx.index().get(1).getText());
            return FpExprs.PositiveInfinity(FpExprs.FpType(eb, sb));
        } else if (getSymbol(ctx.symbol()).equals("-oo")) {
            final var eb = Integer.parseInt(ctx.index().get(0).getText());
            final var sb = Integer.parseInt(ctx.index().get(1).getText());
            return FpExprs.NegativeInfinity(FpExprs.FpType(eb, sb));
        } else if (getSymbol(ctx.symbol()).equals("+zero")) {
            final var eb = Integer.parseInt(ctx.index().get(0).getText());
            final var sb = Integer.parseInt(ctx.index().get(1).getText());
            return FpExprs.PositiveZero(FpExprs.FpType(eb, sb));
        } else if (getSymbol(ctx.symbol()).equals("-zero")) {
            final var eb = Integer.parseInt(ctx.index().get(0).getText());
            final var sb = Integer.parseInt(ctx.index().get(1).getText());
            return FpExprs.NegativeZero(FpExprs.FpType(eb, sb));
        } else {
            return transformSymbol(ctx.symbol(), model, vars);
        }
    }

    protected Expr<?> transformSymbol(
            final SymbolContext ctx, final SmtLibModel model, final Stack<ParamDecl<?>> vars) {
        assert model != null;
        assert vars != null;

        final var value = encodeSymbol(getSymbol(ctx));
        switch (value) {
            case "true":
                return BoolExprs.True();
            case "false":
                return BoolExprs.False();
            default:
                final var filter =
                        vars.toCollection().stream()
                                .filter(it -> it.getName().equals(value))
                                .toList();
                if (!filter.isEmpty()) {
                    final var decl = filter.get(filter.size() - 1);
                    return decl.getRef();
                } else if (symbolTable.definesSymbol(value)) {
                    return symbolTable.getConst(value).getRef();
                } else if (symbolTable.definesEnumLiteral(value)) {
                    return symbolTable.getEnumLiteral(value);
                } else {
                    throw new SmtLibSolverException(
                            "Transformation of symbol not supported: " + value);
                }
        }
    }

    protected Expr<?> transformNumeral(
            final NumeralContext ctx, final SmtLibModel model, final Stack<ParamDecl<?>> vars) {
        assert model != null;
        assert vars != null;

        return Int(ctx.getText());
    }

    protected Expr<?> transformDecimal(
            final DecimalContext ctx, final SmtLibModel model, final Stack<ParamDecl<?>> vars) {
        assert model != null;
        assert vars != null;

        final var decimal = new BigDecimal(ctx.getText());
        if (decimal.scale() <= 0) {
            return Rat(decimal.unscaledValue(), BigInteger.ONE);
        } else {
            return Rat(decimal.unscaledValue(), BigInteger.TEN.pow(decimal.scale()));
        }
    }

    protected Expr<?> transformHexadecimal(
            final HexadecimalContext ctx, final SmtLibModel model, final Stack<ParamDecl<?>> vars) {
        assert model != null;
        assert vars != null;

        final var numStr = ctx.getText().substring(2);
        final var num = new BigInteger(numStr, 16);
        return BvUtils.bigIntegerToNeutralBvLitExpr(num, numStr.length() * 4);
    }

    protected Expr<?> transformBinary(
            final BinaryContext ctx, final SmtLibModel model, final Stack<ParamDecl<?>> vars) {
        assert model != null;
        assert vars != null;

        final var numStr = ctx.getText().substring(2);
        final var num = new BigInteger(numStr, 2);
        return BvUtils.bigIntegerToNeutralBvLitExpr(num, numStr.length());
    }

    protected Type transformSort(final SortContext ctx) {
        final var name = getSymbol(ctx.identifier().symbol());
        switch (name) {
            case "Bool":
                return Bool();
            case "Int":
                return Int();
            case "Real":
                return Rat();
            case "BitVec":
                assert ctx.identifier().index().size() == 1;
                return BvExprs.BvType(Integer.parseInt(ctx.identifier().index().get(0).getText()));
            case "Array":
                assert ctx.sort().size() == 2;
                return Array(transformSort(ctx.sort().get(0)), transformSort(ctx.sort().get(1)));
            default:
                throw new SmtLibSolverException("");
        }
    }

    /* End of visitor implementation */

    /* Variable scope handling */

    protected void pushParams(
            final List<ParamDecl<? extends Type>> paramDecls, Stack<ParamDecl<?>> vars) {
        vars.push();
        vars.add(paramDecls);
    }

    protected void popParams(
            final List<ParamDecl<? extends Type>> paramDecls, Stack<ParamDecl<?>> vars) {
        vars.pop();
    }

    /* Utilities */

    /**
     * We don't want to provide a separate Expr class for these, but we need to parse them.
     *
     * @param funcName: the name of the function to use in backtransformation
     */
    private OperatorCreatorFunction expectedFunc(String funcName) {
        return (params, ops, model, vars) -> {
            var opCnt = ops.size();
            var name = encodeSymbol(funcName + opCnt);
            if (!symbolTable.definesSymbol(name)) {
                Type type = Bool();
                var prefix = "(declare-fun " + name + " (";
                var suffix = ") Bool)";
                for (int i = 0; i < opCnt; i++) {
                    type = FuncType.of(Bool(), type);
                    suffix = " Bool" + suffix;
                }
                symbolTable.put(Const(name, type), name, prefix + suffix);
            }
            Expr<?> expr = symbolTable.getConst(name).getRef();
            for (TermContext op : ops) {
                expr = UnsafeApp(expr, transformTerm(op, model, vars));
            }
            return expr;
        };
    }

    @SuppressWarnings("unused")
    private OperatorCreatorFunction exprNullaryOperator(final Supplier<Expr<?>> function) {
        return (params, ops, model, vars) -> {
            checkArgument(params.size() == 0, "No parameters expected");
            checkArgument(ops.size() == 0, "Nullary operator expected");
            return function.get();
        };
    }

    private OperatorCreatorFunction exprUnaryOperator(final UnaryOperator<Expr<?>> function) {
        return (params, ops, model, vars) -> {
            checkArgument(params.size() == 0, "No parameters expected");
            checkArgument(ops.size() == 1, "Unary operator expected");

            final var op = transformTerm(ops.get(0), model, vars);
            return function.apply(op);
        };
    }

    private OperatorCreatorFunction exprBvExtractOperator() {
        return (params, ops, model, vars) -> {
            checkArgument(params.size() == 2, "Two parameters expected");
            checkArgument(ops.size() == 1, "Unary operator expected");

            final var until = Integer.parseInt(params.get(0).numeral().getText()) + 1;
            final var from = Integer.parseInt(params.get(1).numeral().getText());
            final var extractFrom = castBv(transformTerm(ops.get(0), model, vars));
            return BvExtractExpr.create(extractFrom, Int(from), Int(until));
        };
    }

    private OperatorCreatorFunction exprBvExtendOperator(
            final BiFunction<Expr<?>, BvType, Expr<?>> function) {
        return (params, ops, model, vars) -> {
            checkArgument(params.size() == 1, "One parameters expected");
            checkArgument(ops.size() == 1, "Unary operator expected");

            final var extendWith = Integer.parseInt(params.get(0).numeral().getText());
            final var toExtend = castBv(transformTerm(ops.get(0), model, vars));
            return function.apply(toExtend, BvType.of(toExtend.getType().getSize() + extendWith));
        };
    }

    private OperatorCreatorFunction exprBinaryOperator(final BinaryOperator<Expr<?>> function) {
        return (params, ops, model, vars) -> {
            checkArgument(params.size() == 0, "No parameters expected");
            checkArgument(ops.size() == 2, "Binary operator expected");

            final var op1 = transformTerm(ops.get(0), model, vars);
            final var op2 = transformTerm(ops.get(1), model, vars);
            return function.apply(op1, op2);
        };
    }

    private OperatorCreatorFunction exprRelationalOperator(final BinaryOperator<Expr<?>> function) {
        return (params, ops, model, vars) -> {
            checkArgument(params.size() == 0, "No parameters expected");
            checkArgument(ops.size() == 2, "Binary operator expected");

            final var op1 = transformTerm(ops.get(0), model, vars);
            final var op2 = transformTerm(ops.get(1), model, vars);
            return function.apply(op1, op2);
        };
    }

    private OperatorCreatorFunction exprArrayReadOperator() {
        return (params, ops, model, vars) -> {
            checkArgument(params.size() == 0, "No parameters expected");
            checkArgument(ops.size() == 2, "Binary operator expected");

            final var op1 = transformTerm(ops.get(0), model, vars);
            final var op2 = transformTerm(ops.get(1), model, vars);
            return ArrayReadExpr.create(op1, op2);
        };
    }

    private OperatorCreatorFunction exprMinusOperator() {
        return (params, ops, model, vars) -> {
            checkArgument(params.size() == 0, "No parameters expected");
            checkArgument(ops.size() == 1 || ops.size() == 2, "Unary or binary operator expected");
            if (ops.size() == 2) {
                return exprBinaryOperator(SubExpr::create2).apply(params, ops, model, vars);
            } else {
                return exprUnaryOperator(NegExpr::create2).apply(params, ops, model, vars);
            }
        };
    }

    @SuppressWarnings("unused")
    private OperatorCreatorFunction exprTernaryOperator(final TernaryOperator<Expr<?>> function) {
        return (params, ops, model, vars) -> {
            checkArgument(params.size() == 0, "No parameters expected");
            checkArgument(ops.size() == 3, "Ternary operator expected");
            final Expr<?> op1 = transformTerm(ops.get(0), model, vars);
            final Expr<?> op2 = transformTerm(ops.get(1), model, vars);
            final Expr<?> op3 = transformTerm(ops.get(2), model, vars);
            return function.apply(op1, op2, op3);
        };
    }

    private OperatorCreatorFunction exprIteOperator() {
        return (params, ops, model, vars) -> {
            checkArgument(params.size() == 0, "No parameters expected");
            checkArgument(ops.size() == 3, "Ternary operator expected");

            final var op1 = transformTerm(ops.get(0), model, vars);
            final var op2 = transformTerm(ops.get(1), model, vars);
            final var op3 = transformTerm(ops.get(2), model, vars);
            return IteExpr.create(op1, op2, op3);
        };
    }

    private OperatorCreatorFunction exprArrayWriteOperator() {
        return (params, ops, model, vars) -> {
            checkArgument(params.size() == 0, "No parameters expected");
            checkArgument(ops.size() == 3, "Ternary operator expected");

            final var op1 = transformTerm(ops.get(0), model, vars);
            final var op2 = transformTerm(ops.get(1), model, vars);
            final var op3 = transformTerm(ops.get(2), model, vars);
            return ArrayWriteExpr.create(op1, op2, op3);
        };
    }

    private OperatorCreatorFunction exprMultiaryOperator(
            final Function<List<Expr<?>>, Expr<?>> function) {
        return (params, ops, model, vars) -> {
            checkArgument(params.size() == 0, "No parameters expected");

            return function.apply(
                    ops.stream()
                            .map(op -> transformTerm(op, model, vars))
                            .collect(Collectors.toUnmodifiableList()));
        };
    }

    private OperatorCreatorFunction exprFpLit() {
        return (params, ops, model, vars) -> {
            checkArgument(params.size() == 0, "No parameters expected");
            checkArgument(ops.size() == 3, "Three operators expected");

            final var hidden = (BvLitExpr) transformTerm(ops.get(0), model, vars);
            final var exponent = (BvLitExpr) transformTerm(ops.get(1), model, vars);
            final var significand = (BvLitExpr) transformTerm(ops.get(2), model, vars);

            return FpExprs.Fp(hidden.getValue()[0], exponent, significand);
        };
    }

    private OperatorCreatorFunction exprFpUnaryOperator(
            final BiFunction<FpRoundingMode, Expr<?>, Expr<?>> function) {
        return (params, ops, model, vars) -> {
            checkArgument(params.size() == 0, "No parameters expected");
            checkArgument(ops.size() == 2, "Unary floating point operator expected");

            final var roundingMode = fpOperatorRoundingMode(ops.get(0));
            final var op = transformTerm(ops.get(1), model, vars);
            return function.apply(roundingMode, op);
        };
    }

    private OperatorCreatorFunction exprFpBinaryOperator(
            final TriFunction<FpRoundingMode, Expr<?>, Expr<?>, Expr<?>> function) {
        return (params, ops, model, vars) -> {
            checkArgument(params.size() == 0, "No parameters expected");
            checkArgument(ops.size() == 3, "Binary floating point operator expected");

            final var roundingMode = fpOperatorRoundingMode(ops.get(0));
            final var op1 = transformTerm(ops.get(1), model, vars);
            final var op2 = transformTerm(ops.get(2), model, vars);
            return function.apply(roundingMode, op1, op2);
        };
    }

    private OperatorCreatorFunction exprFpMultiaryOperator(
            final BiFunction<FpRoundingMode, List<Expr<?>>, Expr<?>> function) {
        return (params, ops, model, vars) -> {
            checkArgument(params.size() == 0, "No parameters expected");
            checkArgument(ops.size() >= 1);

            return function.apply(
                    fpOperatorRoundingMode(ops.get(0)),
                    ops.stream()
                            .skip(1)
                            .map(op -> transformTerm(op, model, vars))
                            .collect(Collectors.toUnmodifiableList()));
        };
    }

    private FpRoundingMode fpOperatorRoundingMode(final TermContext term) {
        switch (term.getText()) {
            case "RNE":
                return FpRoundingMode.RNE;
            case "RNA":
                return FpRoundingMode.RNA;
            case "RTP":
                return FpRoundingMode.RTP;
            case "RTN":
                return FpRoundingMode.RTN;
            case "RTZ":
                return FpRoundingMode.RTZ;
            default:
                throw new SmtLibSolverException("");
        }
    }

    static String getSymbol(SymbolContext symbol) {
        final var str = symbol.getText();
        if (symbol.quotedSymbol() != null) {
            assert str.charAt(0) == '|' && str.charAt(str.length() - 1) == '|'
                    : "Quoted symbol not quoted.";
            return str.substring(1, str.length() - 1);
        }
        return str;
    }

    private interface OperatorCreatorFunction
            extends QuadFunction<
                    List<IndexContext>, // Parameters
                    List<TermContext>, // Operands
                    SmtLibModel, // The model
                    Stack<ParamDecl<?>>, // The variable (param) store
                    Expr<?> // Return type
            > {}
}
