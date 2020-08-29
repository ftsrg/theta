package hu.bme.mit.theta.solver.smtlib;

import com.google.common.collect.BiMap;
import com.google.common.collect.HashBiMap;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableMap;
import hu.bme.mit.theta.common.TernaryOperator;
import hu.bme.mit.theta.common.Tuple2;
import hu.bme.mit.theta.core.decl.Decl;
import hu.bme.mit.theta.core.decl.Decls;
import hu.bme.mit.theta.core.decl.ParamDecl;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.abstracttype.AddExpr;
import hu.bme.mit.theta.core.type.abstracttype.DivExpr;
import hu.bme.mit.theta.core.type.abstracttype.EqExpr;
import hu.bme.mit.theta.core.type.abstracttype.GeqExpr;
import hu.bme.mit.theta.core.type.abstracttype.GtExpr;
import hu.bme.mit.theta.core.type.abstracttype.LeqExpr;
import hu.bme.mit.theta.core.type.abstracttype.LtExpr;
import hu.bme.mit.theta.core.type.abstracttype.ModExpr;
import hu.bme.mit.theta.core.type.abstracttype.MulExpr;
import hu.bme.mit.theta.core.type.abstracttype.NegExpr;
import hu.bme.mit.theta.core.type.abstracttype.RemExpr;
import hu.bme.mit.theta.core.type.abstracttype.SubExpr;
import hu.bme.mit.theta.core.type.anytype.IteExpr;
import hu.bme.mit.theta.core.type.arraytype.ArrayExprs;
import hu.bme.mit.theta.core.type.arraytype.ArrayReadExpr;
import hu.bme.mit.theta.core.type.arraytype.ArrayType;
import hu.bme.mit.theta.core.type.arraytype.ArrayWriteExpr;
import hu.bme.mit.theta.core.type.booltype.AndExpr;
import hu.bme.mit.theta.core.type.booltype.BoolExprs;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.type.booltype.IffExpr;
import hu.bme.mit.theta.core.type.booltype.ImplyExpr;
import hu.bme.mit.theta.core.type.booltype.NotExpr;
import hu.bme.mit.theta.core.type.booltype.OrExpr;
import hu.bme.mit.theta.core.type.booltype.XorExpr;
import hu.bme.mit.theta.core.type.bvtype.BvAddExpr;
import hu.bme.mit.theta.core.type.bvtype.BvAndExpr;
import hu.bme.mit.theta.core.type.bvtype.BvArithShiftRightExpr;
import hu.bme.mit.theta.core.type.bvtype.BvDivExpr;
import hu.bme.mit.theta.core.type.bvtype.BvExprs;
import hu.bme.mit.theta.core.type.bvtype.BvGeqExpr;
import hu.bme.mit.theta.core.type.bvtype.BvGtExpr;
import hu.bme.mit.theta.core.type.bvtype.BvLeqExpr;
import hu.bme.mit.theta.core.type.bvtype.BvLogicShiftRightExpr;
import hu.bme.mit.theta.core.type.bvtype.BvLtExpr;
import hu.bme.mit.theta.core.type.bvtype.BvModExpr;
import hu.bme.mit.theta.core.type.bvtype.BvNegExpr;
import hu.bme.mit.theta.core.type.bvtype.BvNotExpr;
import hu.bme.mit.theta.core.type.bvtype.BvOrExpr;
import hu.bme.mit.theta.core.type.bvtype.BvRemExpr;
import hu.bme.mit.theta.core.type.bvtype.BvShiftLeftExpr;
import hu.bme.mit.theta.core.type.bvtype.BvSubExpr;
import hu.bme.mit.theta.core.type.bvtype.BvXorExpr;
import hu.bme.mit.theta.core.type.inttype.IntExprs;
import hu.bme.mit.theta.core.type.inttype.IntToRatExpr;
import hu.bme.mit.theta.core.type.rattype.RatExprs;
import hu.bme.mit.theta.core.utils.BvUtils;
import hu.bme.mit.theta.core.utils.TypeUtils;
import hu.bme.mit.theta.solver.smtlib.dsl.gen.SMTLIBv2BaseVisitor;
import hu.bme.mit.theta.solver.smtlib.dsl.gen.SMTLIBv2Lexer;
import hu.bme.mit.theta.solver.smtlib.dsl.gen.SMTLIBv2Parser;
import hu.bme.mit.theta.solver.smtlib.parser.GetModelResponse;
import hu.bme.mit.theta.solver.smtlib.parser.ThrowExceptionErrorListener;
import org.antlr.v4.runtime.CharStreams;
import org.antlr.v4.runtime.CommonTokenStream;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Map;
import java.util.function.BiFunction;
import java.util.function.BinaryOperator;
import java.util.function.Function;
import java.util.function.Supplier;
import java.util.function.UnaryOperator;
import java.util.stream.Collectors;

import static com.google.common.base.Preconditions.checkArgument;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Exists;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Forall;
import static hu.bme.mit.theta.solver.smtlib.dsl.gen.SMTLIBv2Parser.BinaryContext;
import static hu.bme.mit.theta.solver.smtlib.dsl.gen.SMTLIBv2Parser.DecimalContext;
import static hu.bme.mit.theta.solver.smtlib.dsl.gen.SMTLIBv2Parser.Generic_termContext;
import static hu.bme.mit.theta.solver.smtlib.dsl.gen.SMTLIBv2Parser.HexadecimalContext;
import static hu.bme.mit.theta.solver.smtlib.dsl.gen.SMTLIBv2Parser.IdentifierContext;
import static hu.bme.mit.theta.solver.smtlib.dsl.gen.SMTLIBv2Parser.IndexContext;
import static hu.bme.mit.theta.solver.smtlib.dsl.gen.SMTLIBv2Parser.KeywordContext;
import static hu.bme.mit.theta.solver.smtlib.dsl.gen.SMTLIBv2Parser.NumeralContext;
import static hu.bme.mit.theta.solver.smtlib.dsl.gen.SMTLIBv2Parser.SortContext;
import static hu.bme.mit.theta.solver.smtlib.dsl.gen.SMTLIBv2Parser.StringContext;
import static hu.bme.mit.theta.solver.smtlib.dsl.gen.SMTLIBv2Parser.SymbolContext;
import static hu.bme.mit.theta.solver.smtlib.dsl.gen.SMTLIBv2Parser.TermContext;

public class SmtLibTermTransformer {
    private static final String PARAM_NAME_FORMAT = "_p%d";

    private final SmtLibSymbolTable symbolTable;

    public SmtLibTermTransformer(final SmtLibSymbolTable symbolTable) {
        this.symbolTable = symbolTable;
    }

    public Expr<?> toExpr(final String term, final GetModelResponse model) {
        final var lexer = new SMTLIBv2Lexer(CharStreams.fromString(term));
        final var parser = new SMTLIBv2Parser(new CommonTokenStream(lexer));
        lexer.removeErrorListeners();
        lexer.addErrorListener(new ThrowExceptionErrorListener());
        parser.removeErrorListeners();
        parser.addErrorListener(new ThrowExceptionErrorListener());

        return new TermTransformer(this, model).toExpr(parser.term());
    }

    @SuppressWarnings("unchecked")
    public <I extends Type, E extends Type>  Expr<?> toArrayLitExpr(final String arrayLitImpl, final ArrayType<I, E> type, final GetModelResponse model) {
        final var arrayLitExpr = toExpr(arrayLitImpl, model);
        final var entryExprsBuilder = new ImmutableList.Builder<Tuple2<Expr<I>, Expr<E>>>();

        if(arrayLitExpr instanceof IteExpr) {
            var iteExpr = (IteExpr<E>) arrayLitExpr;
            while (true) {
                entryExprsBuilder.add(Tuple2.of((Expr<I>) iteExpr.getCond().getOps().get(1), iteExpr.getThen()));
                if (iteExpr.getElse() instanceof IteExpr) {
                    iteExpr = (IteExpr<E>) iteExpr.getElse();
                } else {
                    return ArrayExprs.Array(entryExprsBuilder.build(), iteExpr.getElse(), type);
                }
            }
        }
        else {
            return toExpr(arrayLitImpl, model);
        }
    }

    protected ImmutableMap.Builder<String, BiFunction<List<IndexContext>, List<TermContext>, Expr<?>>> configureFunAppTransformer(
        final ImmutableMap.Builder<String, BiFunction<List<IndexContext>, List<TermContext>, Expr<?>>> builder
    ) {
        return builder;
    }

    private static final class TermTransformer extends SMTLIBv2BaseVisitor<Expr<?>> {
        private final BiMap<Decl<?>, String> vars;
        private final GetModelResponse model;
        private static Map<String, BiFunction<List<IndexContext>, List<TermContext>, Expr<?>>> funAppTransformer;

        private final SmtLibTermTransformer that;

        private TermTransformer(final SmtLibTermTransformer that, final GetModelResponse model) {
            this.vars = HashBiMap.create();
            this.model = model;
            this.that = that;

            if(funAppTransformer == null) {
                final var transformer = ImmutableMap.<String, BiFunction<List<IndexContext>, List<TermContext>, Expr<?>>>builder()
                        // Generic
                        .put("ite", exprTernaryOperator(IteExpr::create))

                        // Abstract
                        .put("=", exprBinaryOperator(EqExpr::create2))
                        .put("<=", exprBinaryOperator(LeqExpr::create2))
                        .put("<", exprBinaryOperator(LtExpr::create2))
                        .put(">=", exprBinaryOperator(GeqExpr::create2))
                        .put(">", exprBinaryOperator(GtExpr::create2))
                        .put("+", exprMultiaryOperator(AddExpr::create2))
                        .put("-", exprMinusOperator())
                        .put("*", exprMultiaryOperator(MulExpr::create2))
                        .put("div", exprBinaryOperator(DivExpr::create2))
                        .put("mod", exprBinaryOperator(ModExpr::create2))
                        .put("rem", exprBinaryOperator(RemExpr::create2))

                        // Booleal
                        .put("not", exprUnaryOperator(NotExpr::create))
                        .put("or", exprMultiaryOperator(OrExpr::create))
                        .put("and", exprMultiaryOperator(AndExpr::create))
                        .put("xor", exprBinaryOperator(XorExpr::create))
                        .put("iff", exprBinaryOperator(IffExpr::create))
                        .put("=>", exprBinaryOperator(ImplyExpr::create))

                        // Integer
                        .put("to_real", exprUnaryOperator(IntToRatExpr::create))

                        // Rational

                        // Bitvector
                        .put("bvadd", exprMultiaryOperator(BvAddExpr::create))
                        .put("bvsub", exprBinaryOperator(BvSubExpr::create))
                        .put("bvneg", exprUnaryOperator(BvNegExpr::create))
                        .put("bvmul", exprMultiaryOperator(BvAddExpr::create))
                        .put("bvudiv", exprBinaryOperator(BvDivExpr::create))
                        .put("bvsdiv", exprBinaryOperator(BvDivExpr::create))
                        .put("bvsmod", exprBinaryOperator(BvModExpr::create))
                        .put("bvsrem", exprBinaryOperator(BvRemExpr::create))
                        .put("bvurem", exprBinaryOperator(BvRemExpr::create))
                        .put("bvand", exprMultiaryOperator(BvAndExpr::create))
                        .put("bvor", exprMultiaryOperator(BvOrExpr::create))
                        .put("bvxor", exprMultiaryOperator(BvXorExpr::create))
                        .put("bvnot", exprUnaryOperator(BvNotExpr::create))
                        .put("bvshl", exprBinaryOperator(BvShiftLeftExpr::create))
                        .put("bvashr", exprBinaryOperator(BvArithShiftRightExpr::create))
                        .put("bvlshr", exprBinaryOperator(BvLogicShiftRightExpr::create))
                        .put("bvult", exprBinaryOperator(BvLtExpr::create))
                        .put("bvslt", exprBinaryOperator(BvLtExpr::create))
                        .put("bvule", exprBinaryOperator(BvLeqExpr::create))
                        .put("bvsle", exprBinaryOperator(BvLeqExpr::create))
                        .put("bvugt", exprBinaryOperator(BvGtExpr::create))
                        .put("bvsgt", exprBinaryOperator(BvGtExpr::create))
                        .put("bvuge", exprBinaryOperator(BvGeqExpr::create))
                        .put("bvsge", exprBinaryOperator(BvGeqExpr::create))

                        // Array
                        .put("select", exprBinaryOperator(ArrayReadExpr::create))
                        .put("store", exprTernaryOperator(ArrayWriteExpr::create));

                funAppTransformer = that.configureFunAppTransformer(transformer).build();
            }
        }

        public Expr<?> toExpr(final TermContext ctx) {
            return visitTerm(ctx);
        }

        @Override
        public Expr<?> visitGeneric_term(Generic_termContext ctx) {
            final var funName = ctx.qual_identifier().identifier().symbol().getText();

            final var funParams = ctx.qual_identifier().identifier().index();
            final var funAppParams = ctx.term();

            if (funName.equals("const")) { // as const construct
                final var type = new SortTransformer().visitSort(ctx.qual_identifier().sort());
                final var expr = this.visitTerm(ctx.term().get(0));
                if (type instanceof ArrayType) {
                    return createArrayLitExpr(expr, (ArrayType<?, ?>) type);
                }
                else {
                    throw new UnsupportedOperationException();
                }
            } else if (funAppTransformer.containsKey(funName)) { // known function application
                return funAppTransformer.get(funName).apply(funParams, funAppParams);
            } else { // custom function application
                throw new UnsupportedOperationException();
                /*final Expr<?> funcExpr;
                if (symbolTable.definesSymbol(operation)) {
                    funcExpr = symbolTable.getConst(operation).getRef();
                } else {
                    funcExpr = toFuncLitExpr(funcDecl, model, vars);
                }
                return transformFuncApp(funcExpr, term.getArgs(), model, vars);*/
            }
        }

        @SuppressWarnings("unchecked")
        private <I extends Type, E extends Type> Expr<?> createArrayLitExpr(final Expr<?> elze, final ArrayType<I, E> type) {
            return ArrayExprs.Array(Collections.emptyList(), (Expr<E>) elze, type);
        }

        @Override
        public Expr<?> visitForall_term(SMTLIBv2Parser.Forall_termContext ctx) {
            final var paramDecls = ctx.sorted_var().stream()
                .map(sv -> Decls.Param(sv.symbol().getText(), new SortTransformer().visitSort(sv.sort())))
                .collect(Collectors.toUnmodifiableList());

            pushParams(paramDecls);
            final Expr<BoolType> op = TypeUtils.cast(visitTerm(ctx.term()), Bool());
            popParams(paramDecls);
            return Forall(paramDecls, op);
        }

        @Override
        public Expr<?> visitExists_term(SMTLIBv2Parser.Exists_termContext ctx) {
            final var paramDecls = ctx.sorted_var().stream()
                .map(sv -> Decls.Param(sv.symbol().getText(), new SortTransformer().visitSort(sv.sort())))
                .collect(Collectors.toUnmodifiableList());

            pushParams(paramDecls);
            final Expr<BoolType> op = TypeUtils.cast(visitTerm(ctx.term()), Bool());
            popParams(paramDecls);
            return Exists(paramDecls, op);
        }

        // identifier

        @Override
        public Expr<?> visitIdentifier(IdentifierContext ctx) {
            if(ctx.symbol().getText().equals("as-array")) {
                final var name = ctx.index().get(0).getText();
                return that.toExpr(model.getTerm(name), model);
            }
            else {
                return super.visitIdentifier(ctx);
            }
        }

        // symbol

        @Override
        public Expr<?> visitSymbol(SymbolContext ctx) {
            final var value = ctx.getText();
            switch (value) {
                case "true":
                    return BoolExprs.True();
                case "false":
                    return BoolExprs.False();
                default:
                    throw new UnsupportedOperationException();
            }
        }

        // spec_constant

        @Override
        public Expr<?> visitNumeral(NumeralContext ctx) {
            return IntExprs.Int(ctx.getText());
        }

        @Override
        public Expr<?> visitDecimal(DecimalContext ctx) {
            final var decimal = new BigDecimal(ctx.getText());
            if(decimal.scale() <= 0) {
                return RatExprs.Rat(decimal.unscaledValue(), BigInteger.ONE);
            }
            else {
                return RatExprs.Rat(decimal.unscaledValue(), BigInteger.TEN.pow(decimal.scale()));
            }
        }

        @Override
        public Expr<?> visitHexadecimal(HexadecimalContext ctx) {
            final var numStr = ctx.getText().substring(2);
            final var num = new BigInteger(numStr, 16);
            return BvUtils.bigIntegerToBvLitExpr(num, numStr.length() * 4, false);
        }

        @Override
        public Expr<?> visitBinary(BinaryContext ctx) {
            final var numStr = ctx.getText().substring(2);
            final var num = new BigInteger(numStr, 2);
            return BvUtils.bigIntegerToBvLitExpr(num, numStr.length(), false);
        }

        @Override
        public Expr<?> visitString(StringContext ctx) {
            throw new UnsupportedOperationException();
        }

        @Override
        public Expr<?> visitKeyword(KeywordContext ctx) {
            return super.visitKeyword(ctx);
        }

        ////

        private <T extends Type> void pushParams(final List<ParamDecl<T>> paramDecls) {
            vars.putAll(paramDecls.stream().collect(Collectors.toUnmodifiableMap(Function.identity(), Decl::getName)));
        }

        private <T extends Type> void popParams(final List<ParamDecl<T>> paramDecls) {
            for (final var paramDecl : paramDecls) {
                vars.remove(paramDecl, paramDecl.getName());
            }
        }

        ////

        private BiFunction<List<IndexContext>, List<TermContext>, Expr<?>> exprNullaryOperator(
            final Supplier<Expr<?>> function
        ) {
            return (params, ops) -> {
                checkArgument(params.size() == 0);
                checkArgument(ops.size() == 0);
                return function.get();
            };
        }

        private BiFunction<List<IndexContext>, List<TermContext>, Expr<?>> exprUnaryOperator(
            final UnaryOperator<Expr<?>> function
        ) {
            return (params, ops) -> {
                checkArgument(params.size() == 0);
                checkArgument(ops.size() == 1);
                final Expr<?> op = visitTerm(ops.get(0));
                return function.apply(op);
            };
        }

        private BiFunction<List<IndexContext>, List<TermContext>, Expr<?>> exprBinaryOperator(
            final BinaryOperator<Expr<?>> function
        ) {
            return (params, ops) -> {
                checkArgument(params.size() == 0);
                checkArgument(ops.size() == 2);
                final Expr<?> op1 = visitTerm(ops.get(0));
                final Expr<?> op2 = visitTerm(ops.get(1));
                return function.apply(op1, op2);
            };
        }

        private BiFunction<List<IndexContext>, List<TermContext>, Expr<?>> exprMinusOperator() {
            return (params, ops) -> {
                checkArgument(params.size() == 0);
                checkArgument(ops.size() == 1 || ops.size() == 2);
                if(ops.size() == 2) {
                    final Expr<?> op1 = visitTerm(ops.get(0));
                    final Expr<?> op2 = visitTerm(ops.get(1));
                    return SubExpr.create2(op1, op2);
                }
                else {
                    final Expr<?> op = visitTerm(ops.get(0));
                    return NegExpr.create2(op);
                }
            };
        }

        private BiFunction<List<IndexContext>, List<TermContext>, Expr<?>> exprTernaryOperator(
            final TernaryOperator<Expr<?>> function
        ) {
            return (params, ops) -> {
                checkArgument(params.size() == 0);
                checkArgument(ops.size() == 3);
                final Expr<?> op1 = visitTerm(ops.get(0));
                final Expr<?> op2 = visitTerm(ops.get(1));
                final Expr<?> op3 = visitTerm(ops.get(2));
                return function.apply(op1, op2, op3);
            };
        }

        private BiFunction<List<IndexContext>, List<TermContext>, Expr<?>> exprMultiaryOperator(
            final Function<List<Expr<?>>, Expr<?>> function
        ) {
            return (params, ops) -> {
                checkArgument(params.size() == 0);
                return function.apply(ops.stream().map(this::visitTerm).collect(Collectors.toUnmodifiableList()));
            };
        }
    }

    private static final class SortTransformer extends SMTLIBv2BaseVisitor<Type> {
        @Override
        public Type visitSort(SortContext ctx) {
            final var name = ctx.identifier().symbol().getText();
            switch(name) {
                case "Bool":
                    return BoolExprs.Bool();
                case "Int":
                    return IntExprs.Int();
                case "Real":
                    return RatExprs.Rat();
                case "BitVec":
                    return BvExprs.BvType(Integer.parseInt(ctx.identifier().index().get(0).getText()), false);
                case "Array":
                    return ArrayExprs.Array(this.visitSort(ctx.sort().get(0)), this.visitSort(ctx.sort().get(1)));
                default:
                    throw new UnsupportedOperationException();
            }
        }
    }
}
