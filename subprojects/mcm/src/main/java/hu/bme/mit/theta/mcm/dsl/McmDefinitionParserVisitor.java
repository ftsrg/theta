package hu.bme.mit.theta.mcm.dsl;

import hu.bme.mit.theta.mcm.MCM;
import hu.bme.mit.theta.mcm.dsl.gen.McmDslBaseVisitor;
import hu.bme.mit.theta.mcm.dsl.gen.McmDslParser;
import hu.bme.mit.theta.mcm.graphfilter.*;
import hu.bme.mit.theta.mcm.graphfilter.interfaces.Fence;
import hu.bme.mit.theta.mcm.graphfilter.interfaces.MemoryAccess;
import hu.bme.mit.theta.mcm.graphfilter.interfaces.Read;
import hu.bme.mit.theta.mcm.graphfilter.interfaces.Write;

import java.util.Stack;

public class McmDefinitionParserVisitor<T extends MemoryAccess> extends McmDslBaseVisitor<Filter<T>> {

    private final MCM<T> mcm;

    public McmDefinitionParserVisitor() {
        this.mcm = new MCM<>();
    }

    public MCM<T> getMcm() {
        return mcm;
    }

    @Override
    public Filter<T> visitDefinition(McmDslParser.DefinitionContext ctx) {
        mcm.addDefinition(ctx.name.getText(), ctx.expr().accept(this));
        return null;
    }

    @Override
    public Filter<T> visitNop(McmDslParser.NopContext ctx) {
        return ctx.expr().accept(this);
    }

    @Override
    public Filter<T> visitNextEdge(McmDslParser.NextEdgeContext ctx) {
        return new NextEdge<>(ctx.expr(0).accept(this), ctx.expr(1).accept(this), ctx.namedExpr().name.getText());
    }

    @Override
    public Filter<T> visitSuccessorEdges(McmDslParser.SuccessorEdgesContext ctx) {
        return new SuccessorEdge<>(ctx.expr(0).accept(this), ctx.expr(1).accept(this), ctx.namedExpr().name.getText());
    }

    private final Stack<ForEachVar<T>> forEachVars = new Stack<>();

    @Override
    public Filter<T> visitForEachVar(McmDslParser.ForEachVarContext ctx) {
        forEachVars.push(new ForEachVar<>());
        forEachVars.peek().setOp(ctx.expr().accept(this));
        return forEachVars.pop();
    }

    private final Stack<ForEachThread<T>> forEachThreads = new Stack<>();

    @Override
    public Filter<T> visitForEachThread(McmDslParser.ForEachThreadContext ctx) {
        forEachThreads.push(new ForEachThread<>());
        forEachThreads.peek().setOp(ctx.expr().accept(this));
        return forEachThreads.pop();
    }

    private final Stack<ForEachNode<T>> forEachNodes = new Stack<>();

    @Override
    public Filter<T> visitForEach(McmDslParser.ForEachContext ctx) {
        Filter<T> pattern = ctx.expr(0).accept(this);
        forEachNodes.push(new ForEachNode<>(pattern));
        forEachNodes.peek().setOp(ctx.expr(1).accept(this));
        return forEachNodes.pop();
    }

    @Override
    public Filter<T> visitUnionExpr(McmDslParser.UnionExprContext ctx) {
        return new Union<>(ctx.expr(0).accept(this), ctx.expr(1).accept(this));
    }

    @Override
    public Filter<T> visitSectionExpr(McmDslParser.SectionExprContext ctx) {
        return new Intersection<>(ctx.expr(0).accept(this), ctx.expr(1).accept(this));
    }

    @Override
    public Filter<T> visitSetMinusExpr(McmDslParser.SetMinusExprContext ctx) {
        return new SetMinus<>(ctx.expr(0).accept(this), ctx.expr(1).accept(this));
    }

    @Override
    public Filter<T> visitMultiplyExpr(McmDslParser.MultiplyExprContext ctx) {
        return new Multiply<>(ctx.expr(0).accept(this), ctx.expr(1).accept(this));
    }

    @Override
    public Filter<T> visitSourceExpr(McmDslParser.SourceExprContext ctx) {
        return new Source<>(ctx.expr().accept(this));
    }

    @Override
    public Filter<T> visitTargetExpr(McmDslParser.TargetExprContext ctx) {
        return new Target<>(ctx.expr().accept(this));
    }

    @Override
    public Filter<T> visitSimpleExpr(McmDslParser.SimpleExprContext ctx) {
        if(ctx.EMPTYSET() != null) return new EmptySet<>();
        return super.visitSimpleExpr(ctx);
    }

    @Override
    public Filter<T> visitNamedExpr(McmDslParser.NamedExprContext ctx) {
        if(ctx.name.getText().equals(ctx.name.getText().toUpperCase())) {
            switch(ctx.name.getText()) {
                case "W": return new NamedNode<>(Write.class);
                case "R": return new NamedNode<>(Read.class);
                case "F": return new NamedNode<>(Fence.class);
                case "A": return new NamedNode<>(null);
                default: throw new UnsupportedOperationException("Named node is not a write, read or fence!");
            }
        }
        else {
            return new NamedEdge<>(ctx.name.getText());
        }
    }

    @Override
    public Filter<T> visitTaggedExpr(McmDslParser.TaggedExprContext ctx) {
        return null;
    }
}
