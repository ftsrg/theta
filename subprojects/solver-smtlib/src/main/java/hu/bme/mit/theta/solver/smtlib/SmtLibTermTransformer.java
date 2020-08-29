package hu.bme.mit.theta.solver.smtlib;

import com.google.common.collect.BiMap;
import com.google.common.collect.HashBiMap;
import com.google.common.collect.ImmutableList;
import hu.bme.mit.theta.common.QuadFunction;
import hu.bme.mit.theta.common.TernaryOperator;
import hu.bme.mit.theta.common.Tuple2;
import hu.bme.mit.theta.core.decl.Decl;
import hu.bme.mit.theta.core.decl.Decls;
import hu.bme.mit.theta.core.decl.ParamDecl;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.LitExpr;
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
import hu.bme.mit.theta.core.type.bvtype.BvLitExpr;
import hu.bme.mit.theta.core.type.bvtype.BvLogicShiftRightExpr;
import hu.bme.mit.theta.core.type.bvtype.BvLtExpr;
import hu.bme.mit.theta.core.type.bvtype.BvModExpr;
import hu.bme.mit.theta.core.type.bvtype.BvNegExpr;
import hu.bme.mit.theta.core.type.bvtype.BvNotExpr;
import hu.bme.mit.theta.core.type.bvtype.BvOrExpr;
import hu.bme.mit.theta.core.type.bvtype.BvRemExpr;
import hu.bme.mit.theta.core.type.bvtype.BvShiftLeftExpr;
import hu.bme.mit.theta.core.type.bvtype.BvSubExpr;
import hu.bme.mit.theta.core.type.bvtype.BvType;
import hu.bme.mit.theta.core.type.bvtype.BvXorExpr;
import hu.bme.mit.theta.core.type.inttype.IntExprs;
import hu.bme.mit.theta.core.type.inttype.IntToRatExpr;
import hu.bme.mit.theta.core.type.rattype.RatExprs;
import hu.bme.mit.theta.core.utils.BvUtils;
import hu.bme.mit.theta.core.utils.ExprUtils;
import hu.bme.mit.theta.solver.smtlib.dsl.gen.SMTLIBv2Lexer;
import hu.bme.mit.theta.solver.smtlib.dsl.gen.SMTLIBv2Parser;
import hu.bme.mit.theta.solver.smtlib.parser.GetModelResponse;
import hu.bme.mit.theta.solver.smtlib.parser.ThrowExceptionErrorListener;
import org.antlr.v4.runtime.CharStreams;
import org.antlr.v4.runtime.CommonTokenStream;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.function.BinaryOperator;
import java.util.function.Function;
import java.util.function.Supplier;
import java.util.function.UnaryOperator;
import java.util.stream.Collectors;

import static com.google.common.base.Preconditions.checkArgument;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Exists;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Forall;
import static hu.bme.mit.theta.core.type.bvtype.BvExprs.Bv;
import static hu.bme.mit.theta.core.utils.TypeUtils.cast;
import static hu.bme.mit.theta.solver.smtlib.dsl.gen.SMTLIBv2Parser.BinaryContext;
import static hu.bme.mit.theta.solver.smtlib.dsl.gen.SMTLIBv2Parser.DecimalContext;
import static hu.bme.mit.theta.solver.smtlib.dsl.gen.SMTLIBv2Parser.Exists_termContext;
import static hu.bme.mit.theta.solver.smtlib.dsl.gen.SMTLIBv2Parser.Forall_termContext;
import static hu.bme.mit.theta.solver.smtlib.dsl.gen.SMTLIBv2Parser.Generic_termContext;
import static hu.bme.mit.theta.solver.smtlib.dsl.gen.SMTLIBv2Parser.HexadecimalContext;
import static hu.bme.mit.theta.solver.smtlib.dsl.gen.SMTLIBv2Parser.IdentifierContext;
import static hu.bme.mit.theta.solver.smtlib.dsl.gen.SMTLIBv2Parser.IndexContext;
import static hu.bme.mit.theta.solver.smtlib.dsl.gen.SMTLIBv2Parser.NumeralContext;
import static hu.bme.mit.theta.solver.smtlib.dsl.gen.SMTLIBv2Parser.Qual_identifierContext;
import static hu.bme.mit.theta.solver.smtlib.dsl.gen.SMTLIBv2Parser.SortContext;
import static hu.bme.mit.theta.solver.smtlib.dsl.gen.SMTLIBv2Parser.Spec_constantContext;
import static hu.bme.mit.theta.solver.smtlib.dsl.gen.SMTLIBv2Parser.SymbolContext;
import static hu.bme.mit.theta.solver.smtlib.dsl.gen.SMTLIBv2Parser.TermContext;

public class SmtLibTermTransformer {
    protected static final String PARAM_NAME_FORMAT = "_p%d";

    protected final SmtLibSymbolTable symbolTable;
    protected final Map<String, QuadFunction<List<IndexContext>, List<TermContext>, GetModelResponse, BiMap<Decl<?>, String>, Expr<?>>> funAppTransformer;

    public SmtLibTermTransformer(final SmtLibSymbolTable symbolTable) {
        this.symbolTable = symbolTable;
        this.funAppTransformer = new HashMap<>();

        // Generic
        this.funAppTransformer.put("ite", exprTernaryOperator(IteExpr::create));

        // Abstract
        this.funAppTransformer.put("=", exprBinaryOperator(EqExpr::create2));
        this.funAppTransformer.put("<=", exprBinaryOperator(LeqExpr::create2));
        this.funAppTransformer.put("<", exprBinaryOperator(LtExpr::create2));
        this.funAppTransformer.put(">=", exprBinaryOperator(GeqExpr::create2));
        this.funAppTransformer.put(">", exprBinaryOperator(GtExpr::create2));
        this.funAppTransformer.put("+", exprMultiaryOperator(AddExpr::create2));
        this.funAppTransformer.put("-", exprMinusOperator());
        this.funAppTransformer.put("*", exprMultiaryOperator(MulExpr::create2));
        this.funAppTransformer.put("div", exprBinaryOperator(DivExpr::create2));
        this.funAppTransformer.put("mod", exprBinaryOperator(ModExpr::create2));
        this.funAppTransformer.put("rem", exprBinaryOperator(RemExpr::create2));

        // Booleal
        this.funAppTransformer.put("not", exprUnaryOperator(NotExpr::create));
        this.funAppTransformer.put("or", exprMultiaryOperator(OrExpr::create));
        this.funAppTransformer.put("and", exprMultiaryOperator(AndExpr::create));
        this.funAppTransformer.put("xor", exprBinaryOperator(XorExpr::create));
        this.funAppTransformer.put("iff", exprBinaryOperator(IffExpr::create));
        this.funAppTransformer.put("=>", exprBinaryOperator(ImplyExpr::create));

        // Integer
        this.funAppTransformer.put("to_real", exprUnaryOperator(IntToRatExpr::create));

        // Rational

        // Bitvector
        this.funAppTransformer.put("bvadd", exprMultiaryOperator(BvAddExpr::create));
        this.funAppTransformer.put("bvsub", exprBinaryOperator(BvSubExpr::create));
        this.funAppTransformer.put("bvneg", exprUnaryOperator(BvNegExpr::create));
        this.funAppTransformer.put("bvmul", exprMultiaryOperator(BvAddExpr::create));
        this.funAppTransformer.put("bvudiv", exprBinaryOperator(BvDivExpr::create));
        this.funAppTransformer.put("bvsdiv", exprBinaryOperator(BvDivExpr::create));
        this.funAppTransformer.put("bvsmod", exprBinaryOperator(BvModExpr::create));
        this.funAppTransformer.put("bvsrem", exprBinaryOperator(BvRemExpr::create));
        this.funAppTransformer.put("bvurem", exprBinaryOperator(BvRemExpr::create));
        this.funAppTransformer.put("bvand", exprMultiaryOperator(BvAndExpr::create));
        this.funAppTransformer.put("bvor", exprMultiaryOperator(BvOrExpr::create));
        this.funAppTransformer.put("bvxor", exprMultiaryOperator(BvXorExpr::create));
        this.funAppTransformer.put("bvnot", exprUnaryOperator(BvNotExpr::create));
        this.funAppTransformer.put("bvshl", exprBinaryOperator(BvShiftLeftExpr::create));
        this.funAppTransformer.put("bvashr", exprBinaryOperator(BvArithShiftRightExpr::create));
        this.funAppTransformer.put("bvlshr", exprBinaryOperator(BvLogicShiftRightExpr::create));
        this.funAppTransformer.put("bvult", exprBinaryOperator(BvLtExpr::create));
        this.funAppTransformer.put("bvslt", exprBinaryOperator(BvLtExpr::create));
        this.funAppTransformer.put("bvule", exprBinaryOperator(BvLeqExpr::create));
        this.funAppTransformer.put("bvsle", exprBinaryOperator(BvLeqExpr::create));
        this.funAppTransformer.put("bvugt", exprBinaryOperator(BvGtExpr::create));
        this.funAppTransformer.put("bvsgt", exprBinaryOperator(BvGtExpr::create));
        this.funAppTransformer.put("bvuge", exprBinaryOperator(BvGeqExpr::create));
        this.funAppTransformer.put("bvsge", exprBinaryOperator(BvGeqExpr::create));

        // Array
        this.funAppTransformer.put("select", exprBinaryOperator(ArrayReadExpr::create));
        this.funAppTransformer.put("store", exprTernaryOperator(ArrayWriteExpr::create));
    }

    /* Public interface */

    public Expr<?> toExpr(final String term, final GetModelResponse model) {
        final var lexer = new SMTLIBv2Lexer(CharStreams.fromString(term));
        final var parser = new SMTLIBv2Parser(new CommonTokenStream(lexer));
        lexer.removeErrorListeners();
        lexer.addErrorListener(new ThrowExceptionErrorListener());
        parser.removeErrorListeners();
        parser.addErrorListener(new ThrowExceptionErrorListener());

        return transformTerm(parser.term(), model, HashBiMap.create());
    }

    public <T extends Type> LitExpr<T> toLitExpr(final String litImpl, final T type, final GetModelResponse model) {
        final var litExpr = toExpr(litImpl, model);

        if(litExpr instanceof LitExpr) {
            return (LitExpr<T>) cast(litExpr, type);
        }
        else {
            return (LitExpr<T>) cast(ExprUtils.simplify(litExpr), type);
        }
    }

    @SuppressWarnings("unchecked")
    public <I extends Type, E extends Type>  LitExpr<ArrayType<I, E>> toArrayLitExpr(final String arrayLitImpl, final ArrayType<I, E> type, final GetModelResponse model) {
        final var arrayLitExpr = toExpr(arrayLitImpl, model);

        if(arrayLitExpr instanceof IteExpr) {
            final var entryExprsBuilder = new ImmutableList.Builder<Tuple2<Expr<I>, Expr<E>>>();
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
            return (LitExpr<ArrayType<I, E>>) cast(ExprUtils.simplify(arrayLitExpr), type);
        }
    }

    public LitExpr<BvType> toBvLitExpr(final String bvLitImpl, final BvType type, final GetModelResponse model) {
        final var bvLitExpr = toExpr(bvLitImpl, model);

        if(bvLitExpr instanceof BvLitExpr) {
            return Bv(((BvLitExpr) bvLitExpr).getValue(), type.isSigned());
        }
        else {
            return (LitExpr<BvType>) cast(ExprUtils.simplify(bvLitExpr), type);
        }
    }

    /* End of public interface */

    /* Visitor implementation */

    protected Expr<?> transformTerm(final TermContext ctx, final GetModelResponse model, final BiMap<Decl<?>, String> vars) {
        if(ctx.spec_constant() != null) {
            return transformSpecConstant(ctx.spec_constant(), model, vars);
        }
        else if(ctx.qual_identifier() != null) {
            return transformQualIdentifier(ctx.qual_identifier(), model, vars);
        }
        else if(ctx.generic_term() != null) {
            return transformGenericTerm(ctx.generic_term(), model, vars);
        }
        else if(ctx.let_term() != null) {
            throw new UnsupportedOperationException();
        }
        else if(ctx.forall_term() != null) {
            return transformForallTerm(ctx.forall_term(), model, vars);
        }
        else if(ctx.exists_term() != null) {
            return transformExistsTerm(ctx.exists_term(), model, vars);
        }
        else if(ctx.match_term() != null) {
            throw new UnsupportedOperationException();
        }
        else if(ctx.annotate_term() != null) {
            throw new UnsupportedOperationException();
        }
        else {
            throw new SmtLibSolverException("Invalid input");
        }
    }

    protected Expr<?> transformSpecConstant(final Spec_constantContext ctx, final GetModelResponse model, final BiMap<Decl<?>, String> vars) {
        if(ctx.numeral() != null) {
            return transformNumeral(ctx.numeral(), model, vars);
        }
        else if(ctx.decimal() != null) {
            return transformDecimal(ctx.decimal(), model, vars);
        }
        else if(ctx.hexadecimal() != null) {
            return transformHexadecimal(ctx.hexadecimal(), model, vars);
        }
        else if(ctx.binary() != null) {
            return transformBinary(ctx.binary(), model, vars);
        }
        else if(ctx.string() != null) {
            throw new UnsupportedOperationException();
        }
        else {
            throw new SmtLibSolverException("Invalid input");
        }
    }

    protected Expr<?> transformQualIdentifier(final Qual_identifierContext ctx, final GetModelResponse model, final BiMap<Decl<?>, String> vars) {
        return transformIdentifier(ctx.identifier(), model, vars);
    }

    protected Expr<?> transformGenericTerm(final Generic_termContext ctx, final GetModelResponse model, final BiMap<Decl<?>, String> vars) {
        final var funName = ctx.qual_identifier().identifier().symbol().getText();

        final var funParams = ctx.qual_identifier().identifier().index();
        final var funAppParams = ctx.term();

        if (funName.equals("const")) { // as const construct
            final var type = transformSort(ctx.qual_identifier().sort());
            final var expr = transformTerm(ctx.term().get(0), model, vars);
            if (type instanceof ArrayType) {
                return createArrayLitExpr(expr, (ArrayType<?, ?>) type);
            }
            else {
                throw new UnsupportedOperationException();
            }
        } else if (funAppTransformer.containsKey(funName)) { // known function application
            return funAppTransformer.get(funName).apply(funParams, funAppParams, model, vars);
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

    protected Expr<?> transformForallTerm(final Forall_termContext ctx, final GetModelResponse model, final BiMap<Decl<?>, String> vars) {
        final var paramDecls = ctx.sorted_var().stream()
            .map(sv -> Decls.Param(sv.symbol().getText(), transformSort(sv.sort())))
            .collect(Collectors.toUnmodifiableList());

        pushParams(paramDecls, vars);
        final Expr<BoolType> op = cast(transformTerm(ctx.term(), model, vars), Bool());
        popParams(paramDecls, vars);
        return Forall(paramDecls, op);
    }

    protected Expr<?> transformExistsTerm(final Exists_termContext ctx, final GetModelResponse model, final BiMap<Decl<?>, String> vars) {
        final var paramDecls = ctx.sorted_var().stream()
            .map(sv -> Decls.Param(sv.symbol().getText(), transformSort(sv.sort())))
            .collect(Collectors.toUnmodifiableList());

        pushParams(paramDecls, vars);
        final Expr<BoolType> op = cast(transformTerm(ctx.term(), model, vars), Bool());
        popParams(paramDecls, vars);
        return Exists(paramDecls, op);
    }

    protected Expr<?> transformIdentifier(final IdentifierContext ctx, final GetModelResponse model, final BiMap<Decl<?>, String> vars) {
        if(ctx.symbol().getText().equals("as-array")) {
            final var name = ctx.index().get(0).getText();
            return toExpr(model.getTerm(name), model);
        }
        else {
            return transformSymbol(ctx.symbol(), model, vars);
        }
    }

    protected Expr<?> transformSymbol(final SymbolContext ctx, final GetModelResponse model, final BiMap<Decl<?>, String> vars) {
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

    protected Expr<?> transformNumeral(final NumeralContext ctx, final GetModelResponse model, final BiMap<Decl<?>, String> vars) {
        return IntExprs.Int(ctx.getText());
    }

    protected Expr<?> transformDecimal(final DecimalContext ctx, final GetModelResponse model, final BiMap<Decl<?>, String> vars) {
        final var decimal = new BigDecimal(ctx.getText());
        if(decimal.scale() <= 0) {
            return RatExprs.Rat(decimal.unscaledValue(), BigInteger.ONE);
        }
        else {
            return RatExprs.Rat(decimal.unscaledValue(), BigInteger.TEN.pow(decimal.scale()));
        }
    }

    protected Expr<?> transformHexadecimal(final HexadecimalContext ctx, final GetModelResponse model, final BiMap<Decl<?>, String> vars) {
        final var numStr = ctx.getText().substring(2);
        final var num = new BigInteger(numStr, 16);
        return BvUtils.bigIntegerToBvLitExpr(num, numStr.length() * 4, false);
    }

    protected Expr<?> transformBinary(final BinaryContext ctx, final GetModelResponse model, final BiMap<Decl<?>, String> vars) {
        final var numStr = ctx.getText().substring(2);
        final var num = new BigInteger(numStr, 2);
        return BvUtils.bigIntegerToBvLitExpr(num, numStr.length(), false);
    }

    protected Type transformSort(SortContext ctx) {
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
                return ArrayExprs.Array(transformSort(ctx.sort().get(0)), transformSort(ctx.sort().get(1)));
            default:
                throw new UnsupportedOperationException();
        }
    }

    /* End of visitor implementation */

    /* Variable scope handling */

    protected <T extends Type> void pushParams(final List<ParamDecl<T>> paramDecls, BiMap<Decl<?>, String> vars) {
        vars.putAll(paramDecls.stream().collect(Collectors.toUnmodifiableMap(Function.identity(), Decl::getName)));
    }

    protected <T extends Type> void popParams(final List<ParamDecl<T>> paramDecls, BiMap<Decl<?>, String> vars) {
        for (final var paramDecl : paramDecls) {
            vars.remove(paramDecl, paramDecl.getName());
        }
    }

    /* Utilities */

    private QuadFunction<List<IndexContext>, List<TermContext>, GetModelResponse, BiMap<Decl<?>, String>, Expr<?>> exprNullaryOperator(
        final Supplier<Expr<?>> function
    ) {
        return (params, ops, model, vars) -> {
            checkArgument(params.size() == 0);
            checkArgument(ops.size() == 0);
            return function.get();
        };
    }

    private QuadFunction<List<IndexContext>, List<TermContext>, GetModelResponse, BiMap<Decl<?>, String>, Expr<?>> exprUnaryOperator(
        final UnaryOperator<Expr<?>> function
    ) {
        return (params, ops, model, vars) -> {
            checkArgument(params.size() == 0);
            checkArgument(ops.size() == 1);
            final Expr<?> op = transformTerm(ops.get(0), model, vars);
            return function.apply(op);
        };
    }

    private QuadFunction<List<IndexContext>, List<TermContext>, GetModelResponse, BiMap<Decl<?>, String>, Expr<?>> exprBinaryOperator(
        final BinaryOperator<Expr<?>> function
    ) {
        return (params, ops, model, vars) -> {
            checkArgument(params.size() == 0);
            checkArgument(ops.size() == 2);
            final Expr<?> op1 = transformTerm(ops.get(0), model, vars);
            final Expr<?> op2 = transformTerm(ops.get(1), model, vars);
            return function.apply(op1, op2);
        };
    }

    private QuadFunction<List<IndexContext>, List<TermContext>, GetModelResponse, BiMap<Decl<?>, String>, Expr<?>> exprMinusOperator() {
        return (params, ops, model, vars) -> {
            checkArgument(params.size() == 0);
            checkArgument(ops.size() == 1 || ops.size() == 2);
            if(ops.size() == 2) {
                final Expr<?> op1 = transformTerm(ops.get(0), model, vars);
                final Expr<?> op2 = transformTerm(ops.get(1), model, vars);
                return SubExpr.create2(op1, op2);
            }
            else {
                final Expr<?> op = transformTerm(ops.get(0), model, vars);
                return NegExpr.create2(op);
            }
        };
    }

    private QuadFunction<List<IndexContext>, List<TermContext>, GetModelResponse, BiMap<Decl<?>, String>, Expr<?>>  exprTernaryOperator(
        final TernaryOperator<Expr<?>> function
    ) {
        return (params, ops, model, vars) -> {
            checkArgument(params.size() == 0);
            checkArgument(ops.size() == 3);
            final Expr<?> op1 = transformTerm(ops.get(0), model, vars);
            final Expr<?> op2 = transformTerm(ops.get(1), model, vars);
            final Expr<?> op3 = transformTerm(ops.get(2), model, vars);
            return function.apply(op1, op2, op3);
        };
    }

    private QuadFunction<List<IndexContext>, List<TermContext>, GetModelResponse, BiMap<Decl<?>, String>, Expr<?>> exprMultiaryOperator(
        final Function<List<Expr<?>>, Expr<?>> function
    ) {
        return (params, ops, model, vars) -> {
            checkArgument(params.size() == 0);
            return function.apply(ops.stream().map(op -> transformTerm(op, model, vars)).collect(Collectors.toUnmodifiableList()));
        };
    }

}
