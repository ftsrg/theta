package hu.bme.mit.theta.mcm.dsl;

import hu.bme.mit.theta.mcm.EdgeDB;
import hu.bme.mit.theta.mcm.MCM;
import hu.bme.mit.theta.mcm.dsl.gen.McmDslBaseVisitor;
import hu.bme.mit.theta.mcm.dsl.gen.McmDslParser;
import org.antlr.v4.runtime.Token;

import java.util.HashMap;
import java.util.Map;
import java.util.Stack;
import java.util.function.UnaryOperator;

public class McmParserVisitor extends McmDslBaseVisitor<UnaryOperator<EdgeDB>> {

    private final MCM mcm;
    private final Map<String, UnaryOperator<EdgeDB>> definitions;

    public McmParserVisitor() {
        mcm = new MCM();
        definitions = new HashMap<>();
    }

    @Override
    protected UnaryOperator<EdgeDB> defaultResult() {
        return edgeDB -> edgeDB;
    }

    @Override
    protected UnaryOperator<EdgeDB> aggregateResult(UnaryOperator<EdgeDB> aggregate, UnaryOperator<EdgeDB> nextResult) {
        return edgeDB -> nextResult.apply(aggregate.apply(edgeDB));
    }

    @Override
    public UnaryOperator<EdgeDB> visitDefinition(McmDslParser.DefinitionContext ctx) {
        UnaryOperator<EdgeDB> ret;
        definitions.put(ctx.name.getText(), ret = super.visitDefinition(ctx));
        return ret;
    }

    @Override
    public UnaryOperator<EdgeDB> visitNextEdge(McmDslParser.NextEdgeContext ctx) {
        return edgeDB -> edgeDB.filterNext(ctx.namedExpr().getText(), ctx.expr(0).accept(this), ctx.expr(1).accept(this));
    }

    @Override
    public UnaryOperator<EdgeDB> visitSucessorEdges(McmDslParser.SucessorEdgesContext ctx) {
        return edgeDB -> edgeDB.filterSuccessors(ctx.namedExpr().getText(), ctx.expr(0).accept(this), ctx.expr(1).accept(this));
    }

    private final Stack<Object> vars = new Stack<>(); // TODO: type

    @Override
    public UnaryOperator<EdgeDB> visitForEachVar(McmDslParser.ForEachVarContext ctx) {
        return edgeDB -> {
            EdgeDB ret = edgeDB;
            for(Object var : edgeDB.getVars()) {
                this.vars.push(var);
                ret = ctx.expr().accept(this).apply(ret);
                this.vars.pop();
            }
            return ret;
        };
    }

    private final Stack<Object> threads = new Stack<>(); // TODO: type

    @Override
    public UnaryOperator<EdgeDB> visitForEachThread(McmDslParser.ForEachThreadContext ctx) {
        return edgeDB -> {
            EdgeDB ret = edgeDB;
            for(Object thread : edgeDB.getThreads()) {
                this.threads.push(thread);
                ret = ctx.expr().accept(this).apply(ret);
                this.threads.pop();
            }
            return ret;
        };
    }

    private final Stack<Object> nodes = new Stack<>(); // TODO: type

    @Override
    public UnaryOperator<EdgeDB> visitForEach(McmDslParser.ForEachContext ctx) {
        return edgeDB -> {
            EdgeDB ret = edgeDB;
            for(Object node : ctx.expr(0).accept(this).apply(edgeDB).getNodes()) {
                this.nodes.push(node);
                ret = ctx.expr(1).accept(this).apply(ret);
                this.nodes.pop();
            }
            return ret;
        };
    }

    @Override
    public UnaryOperator<EdgeDB> visitUnionExpr(McmDslParser.UnionExprContext ctx) {
        return edgeDB -> ctx.expr(0).accept(this).apply(edgeDB).union(ctx.expr(1).accept(this).apply(edgeDB));
    }

    @Override
    public UnaryOperator<EdgeDB> visitSectionExpr(McmDslParser.SectionExprContext ctx) {
        return edgeDB -> ctx.expr(0).accept(this).apply(edgeDB).intersect(ctx.expr(1).accept(this).apply(edgeDB));
    }

    @Override
    public UnaryOperator<EdgeDB> visitSetMinusExpr(McmDslParser.SetMinusExprContext ctx) {
        return edgeDB -> ctx.expr(0).accept(this).apply(edgeDB).minus(ctx.expr(1).accept(this).apply(edgeDB));
    }

    @Override
    public UnaryOperator<EdgeDB> visitMultiplyExpr(McmDslParser.MultiplyExprContext ctx) {
        return edgeDB -> ctx.expr(0).accept(this).apply(edgeDB).multiply(ctx.expr(1).accept(this).apply(edgeDB));
    }

    @Override
    public UnaryOperator<EdgeDB> visitMultiplyLaterExpr(McmDslParser.MultiplyLaterExprContext ctx) {
        return edgeDB -> ctx.expr(0).accept(this).apply(edgeDB).multiplyLater(ctx.expr(1).accept(this).apply(edgeDB));
    }

    @Override
    public UnaryOperator<EdgeDB> visitSimpleExpr(McmDslParser.SimpleExprContext ctx) {
        if(ctx.EMPTYSET() != null) {
            return edgeDB -> EdgeDB.empty();
        } else if(ctx.ASTERISK() != null) {
            return edgeDB -> edgeDB;
        }
        return super.visitSimpleExpr(ctx);
    }

    @Override
    public UnaryOperator<EdgeDB> visitNamedExpr(McmDslParser.NamedExprContext ctx) {
        return edgeDB -> edgeDB.filterNamed(ctx.name.getText());
    }

    @Override
    public UnaryOperator<EdgeDB> visitTaggedExpr(McmDslParser.TaggedExprContext ctx) {
        return edgeDB -> {
            EdgeDB ret = ctx.namedExpr().accept(this).apply(edgeDB);
            for (Token token : ctx.tags) {
                ret = ret.filterTagged(token.getText());
            }
            return ret;
        };
    }

    @Override
    public UnaryOperator<EdgeDB> visitConstraints(McmDslParser.ConstraintsContext ctx) {
        ctx.children.forEach(parseTree -> mcm.addPredicate(edgeDB -> parseTree.accept(this).apply(edgeDB).isOk()));
        return super.visitConstraints(ctx);
    }

    @Override
    public UnaryOperator<EdgeDB> visitAndConstraint(McmDslParser.AndConstraintContext ctx) {
        return edgeDB -> ctx.constraint(0).accept(this).apply(edgeDB).and(ctx.constraint(1).accept(this).apply(edgeDB));
    }

    @Override
    public UnaryOperator<EdgeDB> visitOrConstraint(McmDslParser.OrConstraintContext ctx) {
        return edgeDB -> ctx.constraint(0).accept(this).apply(edgeDB).or(ctx.constraint(1).accept(this).apply(edgeDB));
    }

    @Override
    public UnaryOperator<EdgeDB> visitNotConstraint(McmDslParser.NotConstraintContext ctx) {
        return edgeDB -> ctx.constraint().accept(this).apply(edgeDB).not();
    }

    @Override
    public UnaryOperator<EdgeDB> visitImplyConstraint(McmDslParser.ImplyConstraintContext ctx) {
        return edgeDB -> ctx.constraint(0).accept(this).apply(edgeDB).imply(ctx.constraint(1).accept(this).apply(edgeDB));
    }

    @Override
    public UnaryOperator<EdgeDB> visitSimpleConstraint(McmDslParser.SimpleConstraintContext ctx) {
        UnaryOperator<EdgeDB> ret;
        if(ctx.ACYCLIC() != null) {
            ret = edgeDB -> definitions.get(ctx.name.getText()).apply(edgeDB).isAcyclic();
        }
        else if(ctx.IRREFLEXIVE() != null) {
            ret = edgeDB -> definitions.get(ctx.name.getText()).apply(edgeDB).isIrreflexive();
        }
        else {
            ret = edgeDB -> definitions.get(ctx.name.getText()).apply(edgeDB).isEmpty();
        }

        return ctx.NOT() != null ? (edgeDB -> ret.apply(edgeDB).not()) : ret;

    }

    public MCM getMcm() {
        return mcm;
    }

}
