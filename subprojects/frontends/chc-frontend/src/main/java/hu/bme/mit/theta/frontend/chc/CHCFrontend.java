package hu.bme.mit.theta.frontend.chc;

import com.google.common.collect.ImmutableList;
import hu.bme.mit.theta.chc.frontend.dsl.gen.CHCBaseVisitor;
import hu.bme.mit.theta.chc.frontend.dsl.gen.CHCLexer;
import hu.bme.mit.theta.chc.frontend.dsl.gen.CHCParser;
import hu.bme.mit.theta.common.Tuple2;
import hu.bme.mit.theta.core.decl.ConstDecl;
import hu.bme.mit.theta.core.decl.Decl;
import hu.bme.mit.theta.core.decl.Decls;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.stmt.AssignStmt;
import hu.bme.mit.theta.core.stmt.AssumeStmt;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.booltype.BoolExprs;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.type.bvtype.BvExprs;
import hu.bme.mit.theta.core.type.functype.FuncType;
import hu.bme.mit.theta.core.utils.ExprUtils;
import hu.bme.mit.theta.solver.smtlib.impl.generic.GenericSmtLibSymbolTable;
import hu.bme.mit.theta.solver.smtlib.impl.generic.GenericSmtLibTermTransformer;
import hu.bme.mit.theta.solver.smtlib.impl.generic.GenericSmtLibTypeTransformer;
import hu.bme.mit.theta.solver.smtlib.solver.model.SmtLibModel;
import hu.bme.mit.theta.solver.smtlib.solver.transformer.SmtLibSymbolTable;
import hu.bme.mit.theta.solver.smtlib.solver.transformer.SmtLibTermTransformer;
import hu.bme.mit.theta.solver.smtlib.solver.transformer.SmtLibTypeTransformer;
import hu.bme.mit.theta.xcfa.model.*;
import hu.bme.mit.theta.xcfa.model.utils.XcfaLabelVarReplacer;
import org.antlr.v4.runtime.CharStream;
import org.antlr.v4.runtime.CommonTokenStream;
import org.antlr.v4.runtime.ParserRuleContext;
import org.antlr.v4.runtime.misc.Interval;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import static com.google.common.base.Preconditions.checkArgument;
import static hu.bme.mit.theta.core.type.arraytype.ArrayExprs.Array;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;
import static hu.bme.mit.theta.core.type.rattype.RatExprs.Rat;

public class CHCFrontend extends CHCBaseVisitor<Object> {
    private final GenericSmtLibSymbolTable initialSymbolTable = new GenericSmtLibSymbolTable();
    private GenericSmtLibSymbolTable symbolTable;
    private final SmtLibTypeTransformer typeTransformer = new GenericSmtLibTypeTransformer(null);
    private SmtLibTermTransformer termTransformer = new GenericSmtLibTermTransformer(initialSymbolTable);
    private final SmtLibModel smtLibModel = null; // TODO unnecessary
    private CharStream charStream;
    private XcfaProcedure.Builder builder;
    private final XcfaLocation initLocation = XcfaLocation.create("Init");
    private final XcfaLocation errorLocation = XcfaLocation.create("Err");
    private final Map<String, UPred> locations = new HashMap<>();
    private final boolean underscoreVars = false;

    public CHCFrontend() {
        locations.put(initLocation.getName(), new UPred(initLocation, new ArrayList<>()));
        locations.put(errorLocation.getName(), new UPred(initLocation, new ArrayList<>()));
    }

    public XCFA.Builder buildXcfa(CharStream charStream) {
        XCFA.Builder xcfaBuilder = XCFA.builder();
        xcfaBuilder.setDynamic(true);
        XcfaProcess.Builder procBuilder = XcfaProcess.builder();
        builder = XcfaProcedure.builder();
        builder.setName("benchmark");
        builder.addLoc(initLocation);
        builder.setInitLoc(initLocation);
        builder.addLoc(errorLocation);
        builder.setErrorLoc(errorLocation);
        XcfaLocation finalLocation = XcfaLocation.create("Final");
        builder.addLoc(finalLocation);
        builder.setFinalLoc(finalLocation);
        builder.setRetType(Bool());

        this.charStream = charStream;
        CHCParser parser = new CHCParser(new CommonTokenStream(new CHCLexer(charStream)));
        visit(parser.benchmark());

        procBuilder.addProcedure(builder);
        procBuilder.setMainProcedure(builder);
        xcfaBuilder.addProcess(procBuilder);
        xcfaBuilder.setMainProcess(procBuilder);
        return xcfaBuilder;
    }

    @Override
    public Object visitFun_decl(CHCParser.Fun_declContext ctx) {
        String name = ctx.symbol().getText();
        if (ctx.symbol().quotedSymbol() != null) name = name.replaceAll("\\|", "");
        int i = 0;
        List<VarDecl<?>> vars = new ArrayList<>();
        for (CHCParser.SortContext sort : ctx.sort()) {
            String varName = name + (underscoreVars ? "_" : "") + i++;
            Type type = transformSort(sort);
            VarDecl<?> var = Decls.Var(varName, type);
            vars.add(var);
            builder.createVar(var, null);
            transformConst(Decls.Const(varName, type), initialSymbolTable);
        }
        XcfaLocation location = XcfaLocation.create(name);
        locations.put(name, new UPred(location, vars));
        builder.addLoc(location);
        return super.visitFun_decl(ctx);
    }

    @Override
    public Object visitChc_assert(CHCParser.Chc_assertContext ctx) {
        XcfaLocation from, to;
        List<XcfaLabel> labels = new ArrayList<>();

        if (ctx.chc_tail() != null) {
            System.out.println("induction");
            from = getTailFrom(ctx.chc_tail());
            to = getHeadTo(ctx.chc_head());
            Map<String, VarDecl<?>> vars = createVars(ctx.var_decl());
            labels.addAll(getIncomingAssignments(ctx.chc_tail(), vars));
            labels.addAll(getTailLabels(ctx.chc_tail(), vars));
            labels.addAll(getTargetAssignments(ctx.chc_head(), vars));
        } else {
            System.out.println("fact");
            String locName;
            if (ctx.chc_head() != null) {
                locName = ctx.chc_head().u_pred_atom().u_predicate().getText();
            } else {
                locName = ctx.u_predicate().getText();
            }
            from = initLocation;
            to = locations.get(locName).location;
        }
        XcfaEdge edge = XcfaEdge.of(from, to, labels);
        builder.addEdge(edge);
        return super.visitChc_assert(ctx);
    }

    @Override
    public Object visitChc_query(CHCParser.Chc_queryContext ctx) {
        System.out.println("query");
        XcfaLocation from = getTailFrom(ctx.chc_tail());
        Map<String, VarDecl<?>> vars = createVars(ctx.var_decl());
        List<XcfaLabel> labels = new ArrayList<>();
        labels.addAll(getIncomingAssignments(ctx.chc_tail(), vars));
        labels.addAll(getTailLabels(ctx.chc_tail(), vars));
        XcfaEdge edge = XcfaEdge.of(from, errorLocation, labels);
        builder.addEdge(edge);
        return super.visitChc_query(ctx);
    }

    private List<XcfaLabel> getTailLabels(CHCParser.Chc_tailContext tail, Map<String, VarDecl<?>> localVars) {
        List<XcfaLabel> labels = new ArrayList<>();
        tail.i_formula().forEach(i_formula -> {
            Expr<BoolType> expr = termTransformer.toExpr(getOriginalText(i_formula), BoolExprs.Bool(), smtLibModel);
            List<ConstDecl<?>> exprVars = new ArrayList<>();
            ExprUtils.collectConstants(expr, exprVars); // could also need to collect vars, dunno
            Map<Decl<?>, VarDecl<?>> varsToLocal = new HashMap<>();
            for (Decl<?> var : exprVars) {
                if (localVars.containsKey(var.getName())) {
                    varsToLocal.put(var, localVars.get(var.getName()));
                }
            }
            Expr<BoolType> replacedExpr = XcfaLabelVarReplacer.replaceVars(expr, varsToLocal);
            labels.add(XcfaLabel.Stmt(AssumeStmt.of(replacedExpr)));
        });
        return labels;
    }

    private List<XcfaLabel> getIncomingAssignments(CHCParser.Chc_tailContext tail, Map<String, VarDecl<?>> localVars) {
        List<XcfaLabel> labels = new ArrayList<>();
        UPred from = locations.get(getTailFrom(tail).getName()); // TODO handle non-linear CHCs
        tail.u_pred_atom().forEach(u_pred -> {
            List<? extends VarDecl<?>> params = u_pred.symbol().stream().map(symbol -> localVars.get(symbol.getText())).toList();
            labels.addAll(getParamAssignments(params, from.vars));
        });
        return labels;
    }

    private List<XcfaLabel> getTargetAssignments(CHCParser.Chc_headContext head, Map<String, VarDecl<?>> localVars) {
        List<? extends VarDecl<?>> params = head.u_pred_atom().symbol().stream().map(symbol -> localVars.get(symbol.getText())).toList();
        UPred to = locations.get(getHeadTo(head).getName());
        return getParamAssignments(to.vars, params);
    }

    private List<XcfaLabel> getParamAssignments(List<? extends VarDecl<?>> lhs, List<? extends VarDecl<?>> rhs) {
        List<XcfaLabel> labels = new ArrayList<>();
        for (int i = 0; i < lhs.size(); ++i) {
            labels.add(XcfaLabel.Stmt(AssignStmt.create(lhs.get(i), rhs.get(i).getRef())));
        }
        return labels;
    }

    private XcfaLocation getTailFrom(CHCParser.Chc_tailContext tail) {
        List<XcfaLocation> from = new ArrayList<>();
        if (tail.u_pred_atom() != null && !tail.u_pred_atom().isEmpty()) {
            from.addAll(tail.u_pred_atom().stream().map(p -> locations.get(p.u_predicate().getText()).location).toList());
        } else {
            from.add(initLocation);
        }
        return from.get(0); // TODO handle non-linear CHCs
    }

    private XcfaLocation getHeadTo(CHCParser.Chc_headContext head) {
        return locations.get(head.u_pred_atom().u_predicate().getText()).location;
    }

    private String getOriginalText(ParserRuleContext ctx) {
        return charStream.getText(new Interval(ctx.start.getStartIndex(), ctx.stop.getStopIndex()));
    }

    private Map<String, VarDecl<?>> createVars(List<CHCParser.Var_declContext> var_decls) {
        resetSymbolTable();
        Map<String, VarDecl<?>> vars = new HashMap<>();
        for (CHCParser.Var_declContext var_decl : var_decls) {
            String name = var_decl.symbol().getText();
            String varName = name + (underscoreVars ? "_" : "") + builder.getEdges().size();
            Type type = transformSort(var_decl.sort());
            VarDecl<?> var = Decls.Var(varName, type);
            builder.createVar(var, null);
            transformConst(Decls.Const(name, type), symbolTable);
            vars.put(name, var);
        }
        return vars;
    }

    private void resetSymbolTable() {
        symbolTable = new GenericSmtLibSymbolTable(initialSymbolTable);
        termTransformer = new GenericSmtLibTermTransformer(symbolTable);

    }

    protected Type transformSort(final CHCParser.SortContext ctx) {
        final String name = ctx.identifier().symbol().getText();
        switch (name) {
            case "Int":
                return Int();
            case "Bool":
                return Bool();
            case "Real":
                return Rat();
            case "BitVec":
                assert ctx.identifier().index().size() == 1;
                return BvExprs.BvType(Integer.parseInt(ctx.identifier().index().get(0).getText()));
            case "Array":
                assert ctx.sort().size() == 2;
                return Array(transformSort(ctx.sort().get(0)), transformSort(ctx.sort().get(1)));
            default:
                throw new UnsupportedOperationException();
        }
    }

    private void transformConst(final ConstDecl<?> decl, SmtLibSymbolTable symbolTable) {
        final Type type = decl.getType();

        final Tuple2<List<Type>, Type> extractedTypes = extractTypes(type);
        final List<Type> paramTypes = extractedTypes.get1();
        final Type returnType = extractedTypes.get2();

        final String returnSort = typeTransformer.toSort(returnType);
        final String[] paramSorts = paramTypes.stream().map(typeTransformer::toSort)
                .toArray(String[]::new);

        final String symbolName = decl.getName();
        final String symbolDeclaration = String.format(
                "(declare-fun %s (%s) %s)",
                symbolName, String.join(" ", paramSorts), returnSort
        );
        symbolTable.put(decl, symbolName, symbolDeclaration);
    }

    private Tuple2<List<Type>, Type> extractTypes(final Type type) {
        if (type instanceof FuncType<?, ?>) {
            final FuncType<?, ?> funcType = (FuncType<?, ?>) type;

            final Type paramType = funcType.getParamType();
            final Type resultType = funcType.getResultType();

            checkArgument(!(paramType instanceof FuncType));

            final Tuple2<List<Type>, Type> subResult = extractTypes(resultType);
            final List<Type> paramTypes = subResult.get1();
            final Type newResultType = subResult.get2();
            final List<Type> newParamTypes = ImmutableList.<Type>builder().add(paramType).addAll(paramTypes).build();
            final Tuple2<List<Type>, Type> result = Tuple2.of(newParamTypes, newResultType);

            return result;
        } else {
            return Tuple2.of(ImmutableList.of(), type);
        }
    }
}

class UPred {
    final XcfaLocation location;
    final List<VarDecl<?>> vars;

    UPred(XcfaLocation location, List<VarDecl<?>> vars) {
        this.location = location;
        this.vars = vars;
    }
}