package hu.bme.mit.theta.mcm.dsl;

import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.mcm.AcyclicConstraint;
import hu.bme.mit.theta.mcm.EmptyConstraint;
import hu.bme.mit.theta.mcm.MCM;
import hu.bme.mit.theta.mcm.dsl.gen.McmDslBaseVisitor;
import hu.bme.mit.theta.mcm.dsl.gen.McmDslParser;
import hu.bme.mit.theta.mcm.graphfilter.*;
import hu.bme.mit.theta.mcm.graphfilter.interfaces.Fence;
import hu.bme.mit.theta.mcm.graphfilter.interfaces.Process;
import hu.bme.mit.theta.mcm.graphfilter.interfaces.Read;
import hu.bme.mit.theta.mcm.graphfilter.interfaces.Write;
import org.antlr.v4.runtime.Token;

import java.util.*;

public class McmDefinitionParserVisitor extends McmDslBaseVisitor<Filter> {

    private final MCM mcm;
    private final List<? extends Process> processes;
    private final List<VarDecl<? extends Type>> variables;
    private final Map<String, Filter> definitions;

    public McmDefinitionParserVisitor(List<? extends Process> processes, List<VarDecl<? extends Type>> variables) {
        this.mcm = new MCM();
        this.processes = processes;
        this.variables = variables;
        definitions = new HashMap<>();
    }

    public MCM getMcm() {
        return mcm;
    }

    @Override
    public Filter visitDefinition(McmDslParser.DefinitionContext ctx) {
        definitions.put(ctx.name.getText(), ctx.expr().accept(this));
        return null;
    }

    @Override
    public Filter visitNop(McmDslParser.NopContext ctx) {
        return ctx.expr().accept(this);
    }

    @Override
    public Filter visitNextEdge(McmDslParser.NextEdgeContext ctx) {
        Set<String> names = new HashSet<>();
        ctx.namedExpr().forEach(namedExprContext -> names.add(namedExprContext.getText()));
        return new NextEdge(ctx.expr(0).accept(this), ctx.expr(1).accept(this), names);
    }

    @Override
    public Filter visitSuccessorEdges(McmDslParser.SuccessorEdgesContext ctx) {
        Set<String> names = new HashSet<>();
        ctx.namedExpr().forEach(namedExprContext -> names.add(namedExprContext.getText()));
        return new SuccessorEdge(ctx.expr(0).accept(this), ctx.expr(1).accept(this), names);
    }

    private final Stack<ForEachVar> forEachVars = new Stack<>();

    @Override
    public Filter visitForEachVar(McmDslParser.ForEachVarContext ctx) {
        forEachVars.push(new ForEachVar(variables));
        forEachVars.peek().setOp(ctx.expr().accept(this));
        return forEachVars.pop();
    }

    private final Stack<ForEachThread> forEachThreads = new Stack<>();

    @Override
    public Filter visitForEachThread(McmDslParser.ForEachThreadContext ctx) {
        forEachThreads.push(new ForEachThread(processes));
        forEachThreads.peek().setOp(ctx.expr().accept(this));
        return forEachThreads.pop();
    }

    private final Stack<ForEachNode> forEachNodes = new Stack<>();

    @Override
    public Filter visitForEach(McmDslParser.ForEachContext ctx) {
        Filter pattern = ctx.expr(0).accept(this);
        forEachNodes.push(new ForEachNode(pattern));
        forEachNodes.peek().setOp(ctx.expr(1).accept(this));
        return forEachNodes.pop();
    }

    @Override
    public Filter visitUnionExpr(McmDslParser.UnionExprContext ctx) {
        return new Union(ctx.expr(0).accept(this), ctx.expr(1).accept(this));
    }

    @Override
    public Filter visitSectionExpr(McmDslParser.SectionExprContext ctx) {
        return new Intersection(ctx.expr(0).accept(this), ctx.expr(1).accept(this));
    }

    @Override
    public Filter visitSetMinusExpr(McmDslParser.SetMinusExprContext ctx) {
        return new SetMinus(ctx.expr(0).accept(this), ctx.expr(1).accept(this));
    }

    @Override
    public Filter visitMultiplyExpr(McmDslParser.MultiplyExprContext ctx) {
        return new Multiply(ctx.expr(0).accept(this), ctx.expr(1).accept(this));
    }

    @Override
    public Filter visitSourceExpr(McmDslParser.SourceExprContext ctx) {
        return new Source(ctx.expr().accept(this));
    }

    @Override
    public Filter visitTargetExpr(McmDslParser.TargetExprContext ctx) {
        return new Target(ctx.expr().accept(this));
    }

    @Override
    public Filter visitSimpleExpr(McmDslParser.SimpleExprContext ctx) {
        if(ctx.EMPTYSET() != null) return new EmptySet();
        return super.visitSimpleExpr(ctx);
    }

    @Override
    public Filter visitNamedExpr(McmDslParser.NamedExprContext ctx) {
        if(definitions.containsKey(ctx.name.getText())) {
            return definitions.get(ctx.name.getText());
        }
        else if(ctx.name.getText().equals(ctx.name.getText().toUpperCase())) {
            return getNamedNodeFilter(ctx);
        }
        else {
            return new NamedEdge(ctx.name.getText());
        }
    }

    private Filter getNamedNodeFilter(McmDslParser.NamedExprContext ctx) {
        switch(ctx.name.getText()) {
            case "W": return new NamedNode(Write.class);
            case "R": return new NamedNode(Read.class);
            case "F": return new NamedNode(Fence.class);
            case "A": return new NamedNode(null);
            default: throw new UnsupportedOperationException("Named node is not a write, read or fence!");
        }
    }

    @Override
    public Filter visitTaggedExpr(McmDslParser.TaggedExprContext ctx) {
        Set<Filter> tagSet = new HashSet<>();
        for (Token tag : ctx.tags) {
            switch(tag.getText()) {
                case "var": tagSet.add(new VariableTag(forEachVars.peek())); break;
                case "thrd": tagSet.add(new ThreadTag(forEachThreads.peek())); break;
                case "node": tagSet.add(new NodeTag(forEachNodes.peek())); break;
                default: {
                    if(tag.getText().startsWith("var")) {
                        int index = Integer.parseInt(tag.getText().substring(3));
                        tagSet.add(new VariableTag(forEachVars.get(index)));
                    }
                    else if(tag.getText().startsWith("thrd")) {
                        int index = Integer.parseInt(tag.getText().substring(4));
                        tagSet.add(new ThreadTag(forEachThreads.get(index)));
                    }
                    else if(tag.getText().startsWith("node")) {
                        int index = Integer.parseInt(tag.getText().substring(4));
                        tagSet.add(new NodeTag(forEachNodes.get(index)));
                    }
                    else throw new UnsupportedOperationException("Tag is not a var, thrd or node!");
                }
            }
        }
        return new Tagged(tagSet, getNamedNodeFilter(ctx.namedExpr()));
    }

    @Override
    public Filter visitSimpleConstraint(McmDslParser.SimpleConstraintContext ctx) {
        mcm.addConstraint(ctx.EMPTY() != null ? new EmptyConstraint(definitions.get(ctx.name.getText()), ctx.NOT() != null, ctx.name.getText()) : new AcyclicConstraint(definitions.get(ctx.name.getText()), ctx.NOT() != null, ctx.name.getText()));
        return null;
    }
}
