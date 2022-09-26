package hu.bme.mit.theta.frontend.chc;

import hu.bme.mit.theta.chc.frontend.dsl.gen.CHCBaseVisitor;
import hu.bme.mit.theta.chc.frontend.dsl.gen.CHCLexer;
import hu.bme.mit.theta.chc.frontend.dsl.gen.CHCParser;
import hu.bme.mit.theta.core.decl.Decls;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.stmt.AssumeStmt;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.booltype.BoolExprs;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.type.bvtype.BvExprs;
import hu.bme.mit.theta.solver.smtlib.impl.generic.GenericSmtLibSymbolTable;
import hu.bme.mit.theta.solver.smtlib.impl.generic.GenericSmtLibTermTransformer;
import hu.bme.mit.theta.solver.smtlib.solver.model.SmtLibModel;
import hu.bme.mit.theta.solver.smtlib.solver.transformer.SmtLibTermTransformer;
import hu.bme.mit.theta.xcfa.model.*;
import org.antlr.v4.runtime.CharStream;
import org.antlr.v4.runtime.CommonTokenStream;
import org.antlr.v4.runtime.ParserRuleContext;
import org.antlr.v4.runtime.RuleContext;
import org.antlr.v4.runtime.misc.Interval;

import java.util.*;

import static hu.bme.mit.theta.core.type.arraytype.ArrayExprs.Array;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;
import static hu.bme.mit.theta.core.type.rattype.RatExprs.Rat;

public class CHCFrontend extends CHCBaseVisitor<Object> {
    private final SmtLibTermTransformer termTransformer = new GenericSmtLibTermTransformer(new GenericSmtLibSymbolTable()); // TODO may need to fill this up
    private final SmtLibModel smtLibModel = null; // TODO unnecessary
    private CharStream charStream;
    private XcfaProcedure.Builder builder;
    private final XcfaLocation initLocation = XcfaLocation.create("Init");
    private final XcfaLocation errorLocation = XcfaLocation.create("Err");
    private final Map<String, UPred> locations = new HashMap<>();
    private int varCount = 0;
    List<XcfaEdge> edges = new ArrayList<>(); // TODO remove if no longer necessary for debug reasons

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
            VarDecl<?> var = Decls.Var(name + "_" + i++, transformSort(sort));
            vars.add(var);
            builder.createVar(var, null);
        }
        XcfaLocation location = XcfaLocation.create(name);
        locations.put(name, new UPred(location, vars));
        builder.addLoc(location);
        return super.visitFun_decl(ctx);
    }

    @Override
    public Object visitChc_assert(CHCParser.Chc_assertContext ctx) {
        XcfaLocation from = null, to = null;
        List<XcfaLabel> labels = new ArrayList<>();

        if (ctx.chc_tail() != null) {
            System.out.println("induction");
            from = getTailFrom(ctx.chc_tail());
            to = locations.get(ctx.chc_head().u_pred_atom().u_predicate().getText()).location;
            // TODO assign incoming vars
            List<VarDecl<?>> vars = createVars(ctx.var_decl());

            labels.addAll(getTailLabels(ctx.chc_tail()));
        } else {
            System.out.println("fact");
            String locName;
            if (ctx.chc_head() != null) {
                // TODO may need to declare vars here
                locName = ctx.chc_head().u_pred_atom().u_predicate().getText();
            } else {
                locName = ctx.u_predicate().getText();
            }
            from = initLocation;
            to = locations.get(locName).location;
        }
        if (ctx.chc_head() != null) {
            // TODO assign target vars
            // List<VarDecl<?>> targetVars = locations.get(to).vars;
        }
        XcfaEdge edge = XcfaEdge.of(from, to, labels);
        edges.add(edge);
        builder.addEdge(edge);
        return super.visitChc_assert(ctx);
    }

    @Override
    public Object visitChc_query(CHCParser.Chc_queryContext ctx) {
        System.out.println("query");
        List<VarDecl<?>> vars = createVars(ctx.var_decl());
        List<XcfaLabel> labels = new ArrayList<>();
        // TODO assign incoming vars

        labels.addAll(getTailLabels(ctx.chc_tail()));
        XcfaEdge edge = XcfaEdge.of(getTailFrom(ctx.chc_tail()), errorLocation, labels);
        edges.add(edge);
        builder.addEdge(edge);
        return super.visitChc_query(ctx);
    }

    private List<XcfaLabel> getTailLabels(CHCParser.Chc_tailContext tail) {
        List<XcfaLabel> labels = new ArrayList<>();
        // TODO create labels using symbol table
        /*tail.i_formula().forEach(i_formula -> {
            Expr<BoolType> expr = termTransformer.toExpr(getOriginalText(i_formula), BoolExprs.Bool(), smtLibModel);
            labels.add(XcfaLabel.Stmt(AssumeStmt.of(expr)));
        });*/
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

    private String getOriginalText(ParserRuleContext ctx) {
        return charStream.getText(new Interval(ctx.start.getStartIndex(), ctx.stop.getStopIndex()));
    }

    private List<VarDecl<?>> createVars(List<CHCParser.Var_declContext> var_decls) {
        List<VarDecl<?>> vars = new ArrayList<>();
        for (CHCParser.Var_declContext var_decl : var_decls) {
            VarDecl<?> var = Decls.Var(var_decl.symbol().getText() + varCount++, transformSort(var_decl.sort()));
            vars.add(var);
            builder.createVar(var, null);
        }
        return vars;
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