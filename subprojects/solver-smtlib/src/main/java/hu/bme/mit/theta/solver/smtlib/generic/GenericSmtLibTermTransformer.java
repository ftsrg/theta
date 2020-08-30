package hu.bme.mit.theta.solver.smtlib.generic;

import com.google.common.collect.BiMap;
import com.google.common.collect.HashBiMap;
import com.google.common.collect.ImmutableList;
import hu.bme.mit.theta.common.QuintFunction;
import hu.bme.mit.theta.common.TernaryOperator;
import hu.bme.mit.theta.common.Tuple2;
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
import hu.bme.mit.theta.core.type.anytype.RefExpr;
import hu.bme.mit.theta.core.type.arraytype.ArrayReadExpr;
import hu.bme.mit.theta.core.type.arraytype.ArrayType;
import hu.bme.mit.theta.core.type.arraytype.ArrayWriteExpr;
import hu.bme.mit.theta.core.type.booltype.AndExpr;
import hu.bme.mit.theta.core.type.booltype.BoolExprs;
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
import hu.bme.mit.theta.core.type.functype.FuncExprs;
import hu.bme.mit.theta.core.type.functype.FuncType;
import hu.bme.mit.theta.core.type.inttype.IntToRatExpr;
import hu.bme.mit.theta.core.utils.BvUtils;
import hu.bme.mit.theta.core.utils.ExprUtils;
import hu.bme.mit.theta.solver.smtlib.SmtLibModel;
import hu.bme.mit.theta.solver.smtlib.SmtLibSolverException;
import hu.bme.mit.theta.solver.smtlib.SmtLibSymbolTable;
import hu.bme.mit.theta.solver.smtlib.SmtLibTermTransformer;
import hu.bme.mit.theta.solver.smtlib.dsl.gen.SMTLIBv2Lexer;
import hu.bme.mit.theta.solver.smtlib.dsl.gen.SMTLIBv2Parser;
import hu.bme.mit.theta.solver.smtlib.parser.ThrowExceptionErrorListener;
import org.antlr.v4.runtime.CharStreams;
import org.antlr.v4.runtime.CommonTokenStream;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.function.BinaryOperator;
import java.util.function.Function;
import java.util.function.Supplier;
import java.util.function.UnaryOperator;
import java.util.stream.Collectors;
import java.util.stream.IntStream;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;
import static com.google.common.base.Preconditions.checkState;
import static hu.bme.mit.theta.core.type.arraytype.ArrayExprs.Array;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Exists;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Forall;
import static hu.bme.mit.theta.core.type.bvtype.BvExprs.Bv;
import static hu.bme.mit.theta.core.type.functype.FuncExprs.Func;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;
import static hu.bme.mit.theta.core.type.rattype.RatExprs.Rat;
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
import static java.util.stream.Collectors.toList;

public class GenericSmtLibTermTransformer implements SmtLibTermTransformer {
    protected final SmtLibSymbolTable symbolTable;
    protected final Map<String, OperatorCreatorFunction> funAppTransformer;

    public GenericSmtLibTermTransformer(final SmtLibSymbolTable symbolTable) {
        this.symbolTable = symbolTable;
        this.funAppTransformer = new HashMap<>() {{
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
            put("div", exprBinaryOperator(DivExpr::create2));
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

            // Bitvector
            put("bvadd", exprMultiaryOperator(BvAddExpr::create));
            put("bvsub", exprBinaryOperator(BvSubExpr::create));
            put("bvneg", exprUnaryOperator(BvNegExpr::create));
            put("bvmul", exprMultiaryOperator(BvAddExpr::create));
            put("bvudiv", exprBinaryOperator(BvDivExpr::create));
            put("bvsdiv", exprBinaryOperator(BvDivExpr::create));
            put("bvsmod", exprBinaryOperator(BvModExpr::create));
            put("bvsrem", exprBinaryOperator(BvRemExpr::create));
            put("bvurem", exprBinaryOperator(BvRemExpr::create));
            put("bvand", exprMultiaryOperator(BvAndExpr::create));
            put("bvor", exprMultiaryOperator(BvOrExpr::create));
            put("bvxor", exprMultiaryOperator(BvXorExpr::create));
            put("bvnot", exprUnaryOperator(BvNotExpr::create));
            put("bvshl", exprBinaryOperator(BvShiftLeftExpr::create));
            put("bvashr", exprBinaryOperator(BvArithShiftRightExpr::create));
            put("bvlshr", exprBinaryOperator(BvLogicShiftRightExpr::create));
            put("bvult", exprBinaryOperator(BvLtExpr::create));
            put("bvslt", exprBinaryOperator(BvLtExpr::create));
            put("bvule", exprBinaryOperator(BvLeqExpr::create));
            put("bvsle", exprBinaryOperator(BvLeqExpr::create));
            put("bvugt", exprBinaryOperator(BvGtExpr::create));
            put("bvsgt", exprBinaryOperator(BvGtExpr::create));
            put("bvuge", exprBinaryOperator(BvGeqExpr::create));
            put("bvsge", exprBinaryOperator(BvGeqExpr::create));

            // Array
            put("select", exprArrayReadOperator());
            put("store", exprArrayWriteOperator());
        }};
    }

    /* Public interface */

    @Override
    public <P extends Type, R extends Type> LitExpr<FuncType<P, R>> toFuncLitExpr(final String funcLitImpl, final FuncType<P, R> type, final SmtLibModel model) {
        final var lexer = new SMTLIBv2Lexer(CharStreams.fromString(funcLitImpl));
        final var parser = new SMTLIBv2Parser(new CommonTokenStream(lexer));
        lexer.removeErrorListeners();
        lexer.addErrorListener(new ThrowExceptionErrorListener());
        parser.removeErrorListeners();
        parser.addErrorListener(new ThrowExceptionErrorListener());

        final var litExpr = transformFuncDef(parser.function_def(), type, model, HashBiMap.create());
        if(litExpr == null) {
            return null;
        }
        else if(litExpr instanceof LitExpr) {
            return (LitExpr<FuncType<P, R>>) cast(litExpr, type);
        }
        else {
            return (LitExpr<FuncType<P, R>>) cast(ExprUtils.simplify(litExpr), type);
        }
    }

    @Override
    public Expr<?> toExpr(final String term, final Type type, final SmtLibModel model) {
        final var lexer = new SMTLIBv2Lexer(CharStreams.fromString(term));
        final var parser = new SMTLIBv2Parser(new CommonTokenStream(lexer));
        lexer.removeErrorListeners();
        lexer.addErrorListener(new ThrowExceptionErrorListener());
        parser.removeErrorListeners();
        parser.addErrorListener(new ThrowExceptionErrorListener());

        final var expr = transformTerm(parser.function_def().term(), type, model, HashBiMap.create());
        if(expr == null) {
            return null;
        }
        else {
            return cast(expr, type);
        }
    }

    @Override
    public <T extends Type> LitExpr<T> toLitExpr(final String litImpl, final T type, final SmtLibModel model) {
        final var litExpr = toExpr(litImpl, type, model);

        if(litExpr == null) {
            return null;
        }
        else if(litExpr instanceof LitExpr) {
            return (LitExpr<T>) cast(litExpr, type);
        }
        else {
            return (LitExpr<T>) cast(ExprUtils.simplify(litExpr), type);
        }
    }

    @Override
    @SuppressWarnings("unchecked")
    public <I extends Type, E extends Type>  LitExpr<ArrayType<I, E>> toArrayLitExpr(final String arrayLitImpl, final ArrayType<I, E> type, final SmtLibModel model) {
        final var arrayLitExpr = toExpr(arrayLitImpl, type, model);

        if(arrayLitExpr == null) {
            return null;
        }
        else if(arrayLitExpr instanceof IteExpr) {
            final var entryExprsBuilder = new ImmutableList.Builder<Tuple2<Expr<I>, Expr<E>>>();
            var iteExpr = (IteExpr<E>) arrayLitExpr;
            while (true) {
                entryExprsBuilder.add(Tuple2.of((Expr<I>) iteExpr.getCond().getOps().get(1), iteExpr.getThen()));
                if (iteExpr.getElse() instanceof IteExpr) {
                    iteExpr = (IteExpr<E>) iteExpr.getElse();
                } else {
                    return Array(entryExprsBuilder.build(), iteExpr.getElse(), type);
                }
            }
        }
        else {
            return (LitExpr<ArrayType<I, E>>) cast(ExprUtils.simplify(arrayLitExpr), type);
        }
    }

    @Override
    public LitExpr<BvType> toBvLitExpr(final String bvLitImpl, final BvType type, final SmtLibModel model) {
        final var bvLitExpr = toExpr(bvLitImpl, type, model);

        if(bvLitExpr == null) {
            return null;
        }
        else if(bvLitExpr instanceof BvLitExpr) {
            return Bv(((BvLitExpr) bvLitExpr).getValue(), type.isSigned());
        }
        else {
            return (LitExpr<BvType>) cast(ExprUtils.simplify(bvLitExpr), type);
        }
    }

    /* End of public interface */

    /* Visitor implementation */

    protected Expr<?> transformFuncDef(final SMTLIBv2Parser.Function_defContext ctx, final Type type, final SmtLibModel model, final BiMap<ParamTypeDeducer, String> vars) {
        assert type == null || type instanceof FuncType;
        assert model != null;
        assert vars != null;

        final var funcType = type != null ? (FuncType<?, ?>) type : null;

        final var paramDecls = ctx.sorted_var().stream()
            .map(sv -> new ParamTypeDeducer(
                sv.symbol().getText(), transformSort(sv.sort(),
                funcType != null ? funcType.getParamType() : null))
            )
            .collect(toList());
        checkArgument(paramDecls.size() == 1, "Only unary functions are supported");

        pushParams(paramDecls, vars);
        final var op = transformTerm(ctx.term(), funcType != null ? funcType.getResultType() : type, model, vars);
        popParams(paramDecls, vars);

        if(paramDecls.get(0).isTypeUnknown()) {
            return null;
        }
        else {
            assert op != null;
            return Func(paramDecls.get(0).getParamDecl(), op);
        }
    }

    protected Expr<?> transformTerm(final TermContext ctx, final Type type, final SmtLibModel model, final BiMap<ParamTypeDeducer, String> vars) {
        assert model != null;
        assert vars != null;

        if(ctx.spec_constant() != null) {
            return transformSpecConstant(ctx.spec_constant(), type, model, vars);
        }
        else if(ctx.qual_identifier() != null) {
            return transformQualIdentifier(ctx.qual_identifier(), type, model, vars);
        }
        else if(ctx.generic_term() != null) {
            return transformGenericTerm(ctx.generic_term(), type, model, vars);
        }
        else if(ctx.let_term() != null) {
            throw new UnsupportedOperationException();
        }
        else if(ctx.forall_term() != null) {
            return transformForallTerm(ctx.forall_term(), type, model, vars);
        }
        else if(ctx.exists_term() != null) {
            return transformExistsTerm(ctx.exists_term(), type, model, vars);
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

    protected Expr<?> transformSpecConstant(final Spec_constantContext ctx, final Type type, final SmtLibModel model, final BiMap<ParamTypeDeducer, String> vars) {
        assert model != null;
        assert vars != null;

        if(ctx.numeral() != null) {
            return transformNumeral(ctx.numeral(), type, model, vars);
        }
        else if(ctx.decimal() != null) {
            return transformDecimal(ctx.decimal(), type, model, vars);
        }
        else if(ctx.hexadecimal() != null) {
            return transformHexadecimal(ctx.hexadecimal(), type, model, vars);
        }
        else if(ctx.binary() != null) {
            return transformBinary(ctx.binary(), type, model, vars);
        }
        else if(ctx.string() != null) {
            throw new UnsupportedOperationException();
        }
        else {
            throw new SmtLibSolverException("Invalid input");
        }
    }

    protected Expr<?> transformQualIdentifier(final Qual_identifierContext ctx, final Type type, final SmtLibModel model, final BiMap<ParamTypeDeducer, String> vars) {
        assert model != null;
        assert vars != null;

        return transformIdentifier(ctx.identifier(), type, model, vars);
    }

    protected Expr<?> transformGenericTerm(final Generic_termContext ctx, final Type type, final SmtLibModel model, final BiMap<ParamTypeDeducer, String> vars) {
        assert model != null;
        assert vars != null;

        final var funName = ctx.qual_identifier().identifier().symbol().getText();

        final var funParams = ctx.qual_identifier().identifier().index();
        final var funAppParams = ctx.term();

        if (funName.equals("const")) { // as const construct
            final var constType = transformSort(ctx.qual_identifier().sort(), type);
            if (constType instanceof ArrayType) {
                assert type == null || type.equals(constType);
                checkArgument(funAppParams.size() == 1, "Invalid as const construct");

                final var arrayType = (ArrayType<?, ?>) constType;
                final var expr = transformTerm(funAppParams.get(0), arrayType.getElemType(), model, vars);
                return createArrayLitExpr(expr, (ArrayType<?, ?>) type);
            }
            else {
                throw new UnsupportedOperationException();
            }
        } else if (funAppTransformer.containsKey(funName)) { // known function application
            return funAppTransformer.get(funName).apply(funParams, funAppParams, type, model, vars);
        } else { // custom function application
            checkArgument(funParams.size() == 0, "Custom unary function application cannot vahe parameter");
            checkArgument(funAppParams.size() == 1, "Only unary functions are supported");

            return createFuncAppExpr(funName, funAppParams.get(0), type, model, vars);
        }
    }

    @SuppressWarnings("unchecked")
    private <I extends Type, E extends Type> Expr<?> createArrayLitExpr(final Expr<?> elze, final ArrayType<I, E> type) {
        return Array(Collections.emptyList(), (Expr<E>) elze, type);
    }

    private <P extends Type, R extends Type> Expr<?> createFuncAppExpr(final String funName, final TermContext funAppParam, final Type returnType, final SmtLibModel model, final BiMap<ParamTypeDeducer, String> vars) {

        var paramExpr = transformTerm(funAppParam, null, model, vars);
        final Type paramType = paramExpr != null ? paramExpr.getType() : null;

        final Expr<?> funcExpr;
        if (symbolTable.definesSymbol(funName)) {
            funcExpr = checkNotNull(symbolTable.getConst(funName).getRef());
        } else {
            final var funDefImpl = model.getTerm(funName);
            if(paramType == null || returnType == null) {
                funcExpr = toFuncLitExpr(funDefImpl, null, model);
                if(funcExpr == null) {
                    return null;
                }
            }
            else {
                funcExpr = checkNotNull(toFuncLitExpr(funDefImpl, FuncType.of(paramType, returnType), model), "Unsupported expression: was not able to deduce all types");
            }
        }

        assert funcExpr.getType() instanceof FuncType;
        @SuppressWarnings("unchecked") final var funType = (FuncType<P, R>) funcExpr.getType();
        paramExpr = paramExpr == null ? transformTerm(funAppParam, funType.getParamType(), model, vars) : paramExpr;

        return FuncExprs.App(cast(funcExpr, funType), cast(paramExpr, funType.getParamType()));
    }

    protected Expr<?> transformForallTerm(final Forall_termContext ctx, final Type type, final SmtLibModel model, final BiMap<ParamTypeDeducer, String> vars) {
        assert type == null || type.equals(Bool());
        assert model != null;
        assert vars != null;

        final var paramDecls = ctx.sorted_var().stream()
            .map(sv -> new ParamTypeDeducer(sv.symbol().getText(), transformSort(sv.sort(), null)))
            .collect(toList());

        pushParams(paramDecls, vars);
        final var op = transformTerm(ctx.term(), type, model, vars);
        popParams(paramDecls, vars);

        if(paramDecls.stream().anyMatch(ParamTypeDeducer::isTypeUnknown)) {
            return null;
        }
        else {
            assert op != null;
            return Forall(
                paramDecls.stream().map(ParamTypeDeducer::getParamDecl).collect(Collectors.toUnmodifiableList()),
                cast(op, Bool())
            );
        }
    }

    protected Expr<?> transformExistsTerm(final Exists_termContext ctx, final Type type, final SmtLibModel model, final BiMap<ParamTypeDeducer, String> vars) {
        assert type == null || type.equals(Bool());
        assert model != null;
        assert vars != null;

        final var paramDecls = ctx.sorted_var().stream()
            .map(sv -> new ParamTypeDeducer(sv.symbol().getText(), transformSort(sv.sort(), null)))
            .collect(toList());

        pushParams(paramDecls, vars);
        final var op = transformTerm(ctx.term(), type, model, vars);
        popParams(paramDecls, vars);

        if(paramDecls.stream().anyMatch(ParamTypeDeducer::isTypeUnknown)) {
            return null;
        }
        else {
            assert op != null;
            return Exists(
                paramDecls.stream().map(ParamTypeDeducer::getParamDecl).collect(Collectors.toUnmodifiableList()),
                cast(op, Bool())
            );
        }
    }

    protected Expr<?> transformIdentifier(final IdentifierContext ctx, final Type type, final SmtLibModel model, final BiMap<ParamTypeDeducer, String> vars) {
        assert model != null;
        assert vars != null;

        if(ctx.symbol().getText().equals("as-array")) {
            final var name = ctx.index().get(0).getText();
            return toExpr(model.getTerm(name), type, model);
        }
        else {
            return transformSymbol(ctx.symbol(), type, model, vars);
        }
    }

    protected Expr<?> transformSymbol(final SymbolContext ctx, final Type type, final SmtLibModel model, final BiMap<ParamTypeDeducer, String> vars) {
        assert model != null;
        assert vars != null;

        final var value = ctx.getText();
        switch (value) {
            case "true":
                return BoolExprs.True();
            case "false":
                return BoolExprs.False();
            default:
                if(vars.containsValue(value)) {
                    final var decl = vars.inverse().get(value);
                    if(decl.isTypeUnknown()) {
                        if(type == null) {
                            return null;
                        }
                        else {
                            decl.setType(type);
                            return decl.getRef();
                        }
                    }
                    else {
                        final var ref = decl.getRef();
                        assert type == null || type.equals(ref.getType());
                        return ref;
                    }
                }
                else if(symbolTable.definesSymbol(value)) {
                    final var ref = symbolTable.getConst(value).getRef();
                    assert type == null || type.equals(ref.getType());
                    return ref;
                }
                else {
                    throw new UnsupportedOperationException();
                }
        }
    }

    protected Expr<?> transformNumeral(final NumeralContext ctx, final Type type, final SmtLibModel model, final BiMap<ParamTypeDeducer, String> vars) {
        assert type == null || type.equals(Int());
        assert model != null;
        assert vars != null;

        return Int(ctx.getText());
    }

    protected Expr<?> transformDecimal(final DecimalContext ctx, final Type type, final SmtLibModel model, final BiMap<ParamTypeDeducer, String> vars) {
        assert type == null || type.equals(Rat());
        assert model != null;
        assert vars != null;

        final var decimal = new BigDecimal(ctx.getText());
        if(decimal.scale() <= 0) {
            return Rat(decimal.unscaledValue(), BigInteger.ONE);
        }
        else {
            return Rat(decimal.unscaledValue(), BigInteger.TEN.pow(decimal.scale()));
        }
    }

    protected Expr<?> transformHexadecimal(final HexadecimalContext ctx, final Type type, final SmtLibModel model, final BiMap<ParamTypeDeducer, String> vars) {
        assert type == null || type instanceof BvType;
        assert model != null;
        assert vars != null;

        if(type == null) {
            return null;
        }
        else {
            final var bvType = (BvType) type;
            final var numStr = ctx.getText().substring(2);
            final var num = new BigInteger(numStr, 16);
            checkState(bvType.getSize() == numStr.length() * 4, "Type mismatch");

            return BvUtils.bigIntegerToBvLitExpr(num, bvType.getSize(), bvType.isSigned());
        }
    }

    protected Expr<?> transformBinary(final BinaryContext ctx, final Type type, final SmtLibModel model, final BiMap<ParamTypeDeducer, String> vars) {
        assert type == null || type instanceof BvType;
        assert model != null;
        assert vars != null;

        if(type == null) {
            return null;
        }
        else {
            final var bvType = (BvType) type;
            final var numStr = ctx.getText().substring(2);
            final var num = new BigInteger(numStr, 2);
            checkState(bvType.getSize() == numStr.length(), "Type mismatch");

            return BvUtils.bigIntegerToBvLitExpr(num, bvType.getSize(), bvType.isSigned());
        }
    }

    protected Type transformSort(final SortContext ctx, final Type type) {
        final var name = ctx.identifier().symbol().getText();
        switch(name) {
            case "Bool":
                assert type == null || type.equals(Bool());
                return Bool();
            case "Int":
                assert type == null || type.equals(Int());
                return Int();
            case "Real":
                assert type == null || type.equals(Rat());
                return Rat();
            case "BitVec":
                assert type == null || type instanceof BvType;
                if(type == null) {
                    return null;
                }
                else {
                    final var bvType = (BvType) type;
                    checkArgument(Integer.parseInt(ctx.identifier().index().get(0).getText()) == bvType.getSize(), "Type mismatch");
                    return BvExprs.BvType(bvType.getSize(), bvType.isSigned());
                }
            case "Array":
                assert type == null || type instanceof ArrayType<?, ?>;
                if(type == null) {
                    final var indexType = transformSort(ctx.sort().get(0), null);
                    final var elemType = transformSort(ctx.sort().get(1), null);
                    if(indexType == null || elemType == null) {
                        return null;
                    }
                    else {
                        return Array(indexType, elemType);
                    }
                }
                else {
                    final var arrayType = (ArrayType<?, ?>) type;
                    return Array(transformSort(ctx.sort().get(0), arrayType.getIndexType()), transformSort(ctx.sort().get(1), arrayType.getElemType()));
                }
            default:
                throw new UnsupportedOperationException();
        }
    }

    /* End of visitor implementation */

    /* Variable scope handling */

    protected void pushParams(final List<ParamTypeDeducer> paramDecls, BiMap<ParamTypeDeducer, String> vars) {
        vars.putAll(paramDecls.stream().collect(Collectors.toUnmodifiableMap(Function.identity(), ParamTypeDeducer::getName)));
    }

    protected void popParams(final List<ParamTypeDeducer> paramDecls, BiMap<ParamTypeDeducer, String> vars) {
        for (final var paramDecl : paramDecls) {
            vars.remove(paramDecl, paramDecl.getName());
        }
    }

    /* Utilities */

    @SuppressWarnings("unused")
    private OperatorCreatorFunction exprNullaryOperator(final Supplier<Expr<?>> function) {
        return (params, ops, type, model, vars) -> {
            checkArgument(params.size() == 0, "No parameters expected");
            checkArgument(ops.size() == 0, "Nullary operator expected");
            return function.get();
        };
    }

    private OperatorCreatorFunction exprUnaryOperator(final UnaryOperator<Expr<?>> function) {
        return (params, ops, type, model, vars) -> {
            checkArgument(params.size() == 0, "No parameters expected");
            checkArgument(ops.size() == 1, "Unary operator expected");

            if(type == null) {
                final var op = transformTerm(ops.get(0), type, model, vars);
                return function.apply(op);
            }
            else {
                final var op = checkNotNull(transformTerm(ops.get(0), type, model, vars), "Unsupported expression: was not able to deduce all types");
                return function.apply(op);
            }
        };
    }

    private OperatorCreatorFunction exprBinaryOperator(final BinaryOperator<Expr<?>> function) {
        return (params, ops, type, model, vars) -> {
            checkArgument(params.size() == 0, "No parameters expected");
            checkArgument(ops.size() == 2, "Binary operator expected");

            if(type == null) {
                var op1 = transformTerm(ops.get(0), null, model, vars);
                var op2 = transformTerm(ops.get(1), null, model, vars);
                if(op1 == null && op2 == null) {
                    return null;
                }
                else if(op1 != null && op2 == null) {
                    op2 = checkNotNull(transformTerm(ops.get(1), op1.getType(), model, vars), "Unsupported expression: was not able to deduce all types");
                }
                else if(op1 == null /* && op2 != null */) {
                    op1 = checkNotNull(transformTerm(ops.get(0), op2.getType(), model, vars), "Unsupported expression: was not able to deduce all types");
                }
                return function.apply(op1, op2);
            }
            else {
                final var op1 = transformTerm(ops.get(0), type, model, vars);
                final var op2 = transformTerm(ops.get(1), type, model, vars);
                return function.apply(op1, op2);
            }
        };
    }

    private OperatorCreatorFunction exprRelationalOperator(final BinaryOperator<Expr<?>> function) {
        return (params, ops, type, model, vars) -> {
            assert type == null || type.equals(Bool());
            checkArgument(params.size() == 0, "No parameters expected");
            checkArgument(ops.size() == 2, "Binary operator expected");

            var op1 = transformTerm(ops.get(0), null, model, vars);
            var op2 = transformTerm(ops.get(1), null, model, vars);
            if(op1 == null && op2 == null) {
                return null;
            }
            else if(op1 != null && op2 == null) {
                op2 = checkNotNull(transformTerm(ops.get(1), op1.getType(), model, vars), "Unsupported expression: was not able to deduce all types");
            }
            else if(op1 == null /* && op2 != null */) {
                op1 = checkNotNull(transformTerm(ops.get(0), op2.getType(), model, vars), "Unsupported expression: was not able to deduce all types");
            }
            return function.apply(op1, op2);
        };
    }

    private OperatorCreatorFunction exprArrayReadOperator() {
        return (params, ops, type, model, vars) -> {
            checkArgument(params.size() == 0, "No parameters expected");
            checkArgument(ops.size() == 2, "Binary operator expected");

            var op1 = transformTerm(ops.get(0), null, model, vars);
            var op2 = transformTerm(ops.get(1), null, model, vars);
            if(op1 == null && op2 == null) {
                return null;
            }
            else if(op1 != null && op2 == null) {
                assert op1.getType() instanceof ArrayType;
                final var arrayType = (ArrayType<?, ?>) op1.getType();
                op2 = checkNotNull(transformTerm(ops.get(1), arrayType.getIndexType(), model, vars), "Unsupported expression: was not able to deduce all types");
            }
            else if(op1 == null /* && op2 != null */) {
                if(type == null) {
                    return null;
                }
                else {
                    final var arrayType = Array(op2.getType(), type);
                    op1 = checkNotNull(transformTerm(ops.get(0), arrayType, model, vars), "Unsupported expression: was not able to deduce all types");
                }
            }
            return ArrayReadExpr.create(op1, op2);
        };
    }

    private OperatorCreatorFunction exprMinusOperator() {
        return (params, ops, type, model, vars) -> {
            checkArgument(params.size() == 0, "No parameters expected");
            checkArgument(ops.size() == 1 || ops.size() == 2, "Unary or binary operator expected");
            if(ops.size() == 2) {
                return exprBinaryOperator(SubExpr::create2).apply(params, ops, type, model, vars);
            }
            else {
                return exprUnaryOperator(NegExpr::create2).apply(params, ops, type, model, vars);
            }
        };
    }

    @SuppressWarnings("unused")
    private OperatorCreatorFunction exprTernaryOperator(final TernaryOperator<Expr<?>> function) {
        return (params, ops, type, model, vars) -> {
            checkArgument(params.size() == 0, "No parameters expected");
            checkArgument(ops.size() == 3, "Ternary operator expected");
            final Expr<?> op1 = transformTerm(ops.get(0), type, model, vars);
            final Expr<?> op2 = transformTerm(ops.get(1), type, model, vars);
            final Expr<?> op3 = transformTerm(ops.get(2), type, model, vars);
            return function.apply(op1, op2, op3);
        };
    }

    private OperatorCreatorFunction exprIteOperator() {
        return (params, ops, type, model, vars) -> {
            checkArgument(params.size() == 0, "No parameters expected");
            checkArgument(ops.size() == 3, "Ternary operator expected");
            final var op1 = transformTerm(ops.get(0), Bool(), model, vars);
            if(type == null) {
                var op2 = transformTerm(ops.get(1), type, model, vars);
                var op3 = transformTerm(ops.get(2), type, model, vars);
                if(op2 == null && op3 == null) {
                    return null;
                }
                else if(op2 != null && op3 == null) {
                    op3 = checkNotNull(transformTerm(ops.get(2), op2.getType(), model, vars), "Unsupported expression: was not able to deduce all types");
                }
                else if(op2 == null /* && op3 != null */) {
                    op2 = checkNotNull(transformTerm(ops.get(1), op3.getType(), model, vars), "Unsupported expression: was not able to deduce all types");
                }
                return IteExpr.create(op1, op2, op3);
            }
            else {
                final var op2 = transformTerm(ops.get(1), type, model, vars);
                final var op3 = transformTerm(ops.get(2), type, model, vars);
                return IteExpr.create(op1, op2, op3);
            }
        };
    }

    private OperatorCreatorFunction exprArrayWriteOperator() {
        return (params, ops, type, model, vars) -> {
            assert type == null || type instanceof ArrayType;
            checkArgument(params.size() == 0, "No parameters expected");
            checkArgument(ops.size() == 3, "Ternary operator expected");

            if(type == null) {
                var op1 = transformTerm(ops.get(0), null, model, vars);
                var op2 = transformTerm(ops.get(1), null, model, vars);
                var op3 = transformTerm(ops.get(2), null, model, vars);

                if(op1 != null && (op2 == null || op3 == null)) {
                    final var arrayType = (ArrayType<?, ?>) op1.getType();
                    if(op2 == null) {
                        op2 = checkNotNull(transformTerm(ops.get(1), arrayType.getIndexType(), model, vars), "Unsupported expression: was not able to deduce all types");
                    }
                    if(op3 == null) {
                        op3 = checkNotNull(transformTerm(ops.get(2), arrayType.getElemType(), model, vars), "Unsupported expression: was not able to deduce all types");
                    }
                }
                else if(op1 == null && op2 != null && op3 != null) {
                    final var arrayType = Array(op2.getType(), op3.getType());
                    op1 = checkNotNull(transformTerm(ops.get(0), arrayType, model, vars), "Unsupported expression: was not able to deduce all types");
                }
                else {
                    return null;
                }
                return ArrayWriteExpr.create(op1, op2, op3);
            }
            else {
                final var arrayType = (ArrayType<?, ?>) type;
                final var op1 = transformTerm(ops.get(0), arrayType, model, vars);
                final var op2 = transformTerm(ops.get(1), arrayType.getIndexType(), model, vars);
                final var op3 = transformTerm(ops.get(2), arrayType.getElemType(), model, vars);
                return ArrayWriteExpr.create(op1, op2, op3);
            }
        };
    }

    private OperatorCreatorFunction exprMultiaryOperator(final Function<List<Expr<?>>, Expr<?>> function) {
        return (params, ops, type, model, vars) -> {
            checkArgument(params.size() == 0, "No parameters expected");
            if(type == null) {
                final var transformedOps = new ArrayList<Expr<?>>();
                ops.stream()
                    .map(op -> transformTerm(op, type, model, vars))
                    .forEach(transformedOps::add);

                if(transformedOps.stream().allMatch(Objects::isNull)) {
                    return null;
                }
                else {
                    final var opType = transformedOps.stream().filter(Objects::nonNull).findAny().get().getType();
                    return function.apply(IntStream
                        .range(0, ops.size())
                        .mapToObj(i -> transformedOps.get(i) == null ? transformTerm(ops.get(i), opType, model, vars) : transformedOps.get(i))
                        .collect(Collectors.toUnmodifiableList())
                    );
                }
            }
            else {
                return function.apply(ops.stream().map(op -> transformTerm(op, type, model, vars)).collect(Collectors.toUnmodifiableList()));
            }
        };
    }

    private interface OperatorCreatorFunction extends QuintFunction<
        List<IndexContext>,     // Parameters
        List<TermContext>,      // Operands
        Type,                   // Expected type of result
                                                                       SmtLibModel,       // The model
        BiMap<ParamTypeDeducer, String>, // The variable (param) store
        Expr<?>                 // Return type
    > {}

    private final static class ParamTypeDeducer {
        private final String name;
        private Type type;
        private ParamDecl<?> paramDecl;

        public ParamTypeDeducer(final String name, final Type type) {
            this.name = name;
            if(type != null) {
                setType(type);
            }
        }

        public boolean isTypeUnknown() {
            return type == null;
        }

        public void setType(final Type type) {
            checkArgument(type != null);
            checkState(this.type == null);
            this.type = type;
            this.paramDecl = Decls.Param(name, type);
        }

        public String getName() {
            return name;
        }

        public ParamDecl<?> getParamDecl() {
            checkState(paramDecl != null);
            return paramDecl;
        }

        public RefExpr<?> getRef() {
            checkState(paramDecl != null);
            return paramDecl.getRef();
        }
    }

}
