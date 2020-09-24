package hu.bme.mit.theta.mcm.dsl;

import hu.bme.mit.theta.common.Tuple2;
import hu.bme.mit.theta.mcm.MCM;
import hu.bme.mit.theta.mcm.dsl.gen.McmDslBaseVisitor;
import hu.bme.mit.theta.mcm.dsl.gen.McmDslParser;
import hu.bme.mit.theta.mcm.graph.EdgeDB;
import hu.bme.mit.theta.mcm.graph.classification.Thread;
import hu.bme.mit.theta.mcm.graph.classification.Variable;
import hu.bme.mit.theta.mcm.graph.classification.nodes.Node;
import org.antlr.v4.runtime.Token;

import java.util.*;
import java.util.function.UnaryOperator;

public class McmParserVisitor extends McmDslBaseVisitor<UnaryOperator<List<EdgeDB>>> {

    private final MCM mcm;
    private final Map<String, Tuple2<UnaryOperator<List<EdgeDB>>, Set<String>>> definitions;
    private Set<String> currentDefinitionStringSet;
    private Set<String> currentConstraintStringSet;

    public McmParserVisitor() {
        definitions = new HashMap<>();
        mcm = new MCM();
    }

    @Override
    protected UnaryOperator<List<EdgeDB>> defaultResult() {
        return edgeDBList -> edgeDBList;
    }

    @Override
    protected UnaryOperator<List<EdgeDB>> aggregateResult(UnaryOperator<List<EdgeDB>> aggregate, UnaryOperator<List<EdgeDB>> nextResult) {
        return edgeDBList -> nextResult.apply(aggregate.apply(edgeDBList));
    }

    @Override
    public UnaryOperator<List<EdgeDB>> visitDefinition(McmDslParser.DefinitionContext ctx) {
        currentDefinitionStringSet = new HashSet<>();
        UnaryOperator<List<EdgeDB>> ret = super.visitDefinition(ctx);
        definitions.put(ctx.name.getText(), Tuple2.of(ret, currentDefinitionStringSet));
        return ret;
    }

    @Override
    public UnaryOperator<List<EdgeDB>> visitNextEdge(McmDslParser.NextEdgeContext ctx) {
        UnaryOperator<List<EdgeDB>> rhOp = ctx.expr(1).accept(this);
        UnaryOperator<List<EdgeDB>> lhOp = ctx.expr(0).accept(this);
        currentDefinitionStringSet.add(ctx.namedExpr().getText());
        return edgeDBList -> {
            List<EdgeDB> ret = new ArrayList<>();
            for (EdgeDB edgeDB : edgeDBList) {
                List<EdgeDB> lhs = lhOp.apply(List.of(edgeDB));
                List<EdgeDB> rhs = rhOp.apply(List.of(edgeDB));
                for (EdgeDB lh : lhs) {
                    for (EdgeDB rh : rhs) {
                        ret.add(edgeDB.filterNext(ctx.namedExpr().getText(), lh, rh));
                    }
                }
            }
            return ret;
        };
    }

    @Override
    public UnaryOperator<List<EdgeDB>> visitSucessorEdges(McmDslParser.SucessorEdgesContext ctx) {
        UnaryOperator<List<EdgeDB>> rhOp = ctx.expr(1).accept(this);
        UnaryOperator<List<EdgeDB>> lhOp = ctx.expr(0).accept(this);
        currentDefinitionStringSet.add(ctx.namedExpr().getText());  // TODO: rf(R -> W) does not mean rf, R and W are the dependencies, but rather only rf(R -> W)
        return edgeDBList -> {
            List<EdgeDB> ret = new ArrayList<>();
            for (EdgeDB edgeDB : edgeDBList) {
                List<EdgeDB> lhs = lhOp.apply(List.of(edgeDB));
                List<EdgeDB> rhs = rhOp.apply(List.of(edgeDB));
                for (EdgeDB lh : lhs) {
                    for (EdgeDB rh : rhs) {
                        ret.add(edgeDB.filterSuccessors(ctx.namedExpr().getText(), lh, rh));
                    }
                }
            }
            return ret;
        };
    }

    private final Stack<Variable> vars = new Stack<>();

    @Override
    public UnaryOperator<List<EdgeDB>> visitForEachVar(McmDslParser.ForEachVarContext ctx) {
        UnaryOperator<List<EdgeDB>> op = ctx.expr().accept(this);
        return edgeDBList -> {
            List<EdgeDB> ret = new ArrayList<>();
            for(Variable var : edgeDBList.get(0).getVars()) {
                this.vars.push(var);
                ret.addAll(op.apply(edgeDBList));
                this.vars.pop();
            }
            return ret;
        };
    }

    private final Stack<Thread> threads = new Stack<>();

    @Override
    public UnaryOperator<List<EdgeDB>> visitForEachThread(McmDslParser.ForEachThreadContext ctx) {
        UnaryOperator<List<EdgeDB>> op = ctx.expr().accept(this);
        return edgeDBList -> {
            List<EdgeDB> ret = new ArrayList<>();
            for(Thread thread : edgeDBList.get(0).getThreads()) {
                this.threads.push(thread);
                ret.addAll(op.apply(edgeDBList));
                this.threads.pop();
            }
            return ret;
        };
    }

    private final Stack<Node> nodes = new Stack<>();

    @Override
    public UnaryOperator<List<EdgeDB>> visitForEach(McmDslParser.ForEachContext ctx) {
        UnaryOperator<List<EdgeDB>> lhOp = ctx.expr(0).accept(this);
        UnaryOperator<List<EdgeDB>> rhOp = ctx.expr(1).accept(this);
        return edgeDBList -> {
            List<EdgeDB> ret = new ArrayList<>();
            for(Node node : lhOp.apply(edgeDBList).get(0).getNodes()) {
                this.nodes.push(node);
                ret.addAll(rhOp.apply(edgeDBList));
                this.nodes.pop();
            }
            return ret;
        };
    }

    @Override
    public UnaryOperator<List<EdgeDB>> visitUnionExpr(McmDslParser.UnionExprContext ctx) {
        UnaryOperator<List<EdgeDB>> lhOp = ctx.expr(0).accept(this);
        UnaryOperator<List<EdgeDB>> rhOp = ctx.expr(1).accept(this);
        return edgeDBList -> {
            List<EdgeDB> ret = new ArrayList<>();
            for (EdgeDB edgeDB : edgeDBList) {
                List<EdgeDB> lhs = lhOp.apply(List.of(edgeDB));
                List<EdgeDB> rhs = rhOp.apply(List.of(edgeDB));
                for (EdgeDB lh : lhs) {
                    for (EdgeDB rh : rhs) {
                        ret.add(lh.union(rh));
                    }
                }
            }
            return ret;
        };
    }

    @Override
    public UnaryOperator<List<EdgeDB>> visitSectionExpr(McmDslParser.SectionExprContext ctx) {
        UnaryOperator<List<EdgeDB>> lhOp = ctx.expr(0).accept(this);
        UnaryOperator<List<EdgeDB>> rhOp = ctx.expr(1).accept(this);
        return edgeDBList -> {
            List<EdgeDB> ret = new ArrayList<>();
            for (EdgeDB edgeDB : edgeDBList) {
                List<EdgeDB> lhs = lhOp.apply(List.of(edgeDB));
                List<EdgeDB> rhs = rhOp.apply(List.of(edgeDB));
                for (EdgeDB lh : lhs) {
                    for (EdgeDB rh : rhs) {
                        ret.add(lh.intersect(rh));
                    }
                }
            }
            return ret;
        };
    }

    @Override
    public UnaryOperator<List<EdgeDB>> visitSetMinusExpr(McmDslParser.SetMinusExprContext ctx) {
        UnaryOperator<List<EdgeDB>> lhOp = ctx.expr(0).accept(this);
        UnaryOperator<List<EdgeDB>> rhOp = ctx.expr(1).accept(this);
        return edgeDBList -> {
            List<EdgeDB> ret = new ArrayList<>();
            for (EdgeDB edgeDB : edgeDBList) {
                List<EdgeDB> lhs = lhOp.apply(List.of(edgeDB));
                List<EdgeDB> rhs = rhOp.apply(List.of(edgeDB));
                for (EdgeDB lh : lhs) {
                    for (EdgeDB rh : rhs) {
                        ret.add(lh.minus(rh));
                    }
                }
            }
            return ret;
        };
    }

    @Override
    public UnaryOperator<List<EdgeDB>> visitMultiplyExpr(McmDslParser.MultiplyExprContext ctx) {
        UnaryOperator<List<EdgeDB>> lhOp = ctx.expr(0).accept(this);
        UnaryOperator<List<EdgeDB>> rhOp = ctx.expr(1).accept(this);
        return edgeDBList -> {
            List<EdgeDB> ret = new ArrayList<>();
            for (EdgeDB edgeDB : edgeDBList) {
                List<EdgeDB> lhs = lhOp.apply(List.of(edgeDB));
                List<EdgeDB> rhs = rhOp.apply(List.of(edgeDB));
                for (EdgeDB lh : lhs) {
                    for (EdgeDB rh : rhs) {
                        ret.add(lh.multiply(rh, ctx.name.getText()));
                    }
                }
            }
            return ret;
        };
    }

    @Override
    public UnaryOperator<List<EdgeDB>> visitSourceExpr(McmDslParser.SourceExprContext ctx) {
        UnaryOperator<List<EdgeDB>> op = ctx.expr().accept(this);
        return edgeDBList -> {
            List<EdgeDB> ret = new ArrayList<>();
            for (EdgeDB edgeDB : edgeDBList) {
                for (EdgeDB db : op.apply(List.of(edgeDB))) {
                    ret.add(db.filterSource(db));
                }
            }
            return ret;
        };
    }

    @Override
    public UnaryOperator<List<EdgeDB>> visitTargetExpr(McmDslParser.TargetExprContext ctx) {
        UnaryOperator<List<EdgeDB>> op = ctx.expr().accept(this);
        return edgeDBList -> {
            List<EdgeDB> ret = new ArrayList<>();
            for (EdgeDB edgeDB : edgeDBList) {
                for (EdgeDB db : op.apply(List.of(edgeDB))) {
                    ret.add(db.filterTarget(db));
                }
            }
            return ret;
        };
    }

    @Override
    public UnaryOperator<List<EdgeDB>> visitNop(McmDslParser.NopContext ctx) {
        return ctx.expr().accept(this);
    }

    @Override
    public UnaryOperator<List<EdgeDB>> visitSimpleExpr(McmDslParser.SimpleExprContext ctx) {
        if(ctx.EMPTYSET() != null) {
            return edgeDBList -> List.of(EdgeDB.empty());
        }
        return super.visitSimpleExpr(ctx);
    }

    @Override
    public UnaryOperator<List<EdgeDB>> visitNamedExpr(McmDslParser.NamedExprContext ctx) {
        if(definitions.containsKey(ctx.name.getText())) {
            currentDefinitionStringSet.addAll(definitions.get(ctx.name.getText()).get2());
        }
        else {
            currentDefinitionStringSet.add(ctx.name.getText());
        }
        return edgeDBList -> {
            List<EdgeDB> ret = new ArrayList<>();
            for (EdgeDB edgeDB : edgeDBList) {
                if(definitions.containsKey(ctx.name.getText())) {
                    ret.addAll(definitions.get(ctx.name.getText()).get1().apply(List.of(edgeDB)));
                }
                else {
                    ret.add(edgeDB.filterNamed(ctx.name.getText()));
                }
            }
            return ret;
        };
    }

    @Override
    public UnaryOperator<List<EdgeDB>> visitTaggedExpr(McmDslParser.TaggedExprContext ctx) {
        UnaryOperator<List<EdgeDB>> namedOperator = ctx.namedExpr().accept(this);
        return edgeDBList -> {
            List<EdgeDB> retList = new ArrayList<>();
            for (EdgeDB edgeDB : edgeDBList) {
                for (EdgeDB ret : namedOperator.apply(List.of(edgeDB))) {
                    for (Token token : ctx.tags) {
                        if (token.getText().startsWith("thread")) {
                            if (token.getText().equals("thread")) {
                                ret = ret.filterThread(threads.peek());
                            } else {
                                int i = Integer.parseInt(token.getText().substring("thread".length()));
                                ret = ret.filterThread(threads.get(i));
                            }
                        } else if (token.getText().startsWith("var")) {
                            if (token.getText().equals("var")) {
                                ret = ret.filterVar(vars.peek());
                            } else {
                                int i = Integer.parseInt(token.getText().substring("var".length()));
                                ret = ret.filterVar(vars.get(i));
                            }
                        } else if (token.getText().startsWith("node")) {
                            if (token.getText().equals("node")) {
                                ret = ret.filterNode(nodes.peek());
                            } else {
                                int i = Integer.parseInt(token.getText().substring("node".length()));
                                ret = ret.filterNode(nodes.get(i));
                            }
                        } else if (token.getText().equals("new")) {
                            ret = ret.filterNew();
                        }
                    }
                    retList.add(ret);
                }
            }
            return retList;
        };
    }

    @Override
    public UnaryOperator<List<EdgeDB>> visitConstraints(McmDslParser.ConstraintsContext ctx) {
        ctx.children.forEach(parseTree -> {
            currentConstraintStringSet = new HashSet<>();
            UnaryOperator<List<EdgeDB>> accept = parseTree.accept(this);
            mcm.addPredicate(edgeDB -> {
                for (EdgeDB db : accept.apply(List.of(edgeDB))) {
                    if(!db.isOk()) return false;
                }
                return true;
            }, currentConstraintStringSet);
        });
        return super.visitConstraints(ctx);
    }

    @Override
    public UnaryOperator<List<EdgeDB>> visitAndConstraint(McmDslParser.AndConstraintContext ctx) {
        UnaryOperator<List<EdgeDB>> rhOp = ctx.constraint(1).accept(this);
        UnaryOperator<List<EdgeDB>> lhOp = ctx.constraint(0).accept(this);
        return edgeDBList -> {
            for (EdgeDB edgeDB : edgeDBList) {
                List<EdgeDB> lhs = lhOp.apply(List.of(edgeDB));
                List<EdgeDB> rhs = rhOp.apply(List.of(edgeDB));
                for (EdgeDB lh : lhs) {
                    if(!lh.isOk()) {
                        return List.of(EdgeDB.falseValue());
                    }
                }
                for (EdgeDB rh : rhs) {
                    if(!rh.isOk()) {
                        return List.of(EdgeDB.falseValue());
                    }
                }
            }
            return List.of(EdgeDB.trueValue());
        };
    }

    @Override
    public UnaryOperator<List<EdgeDB>> visitOrConstraint(McmDslParser.OrConstraintContext ctx) {
        UnaryOperator<List<EdgeDB>> rhOp = ctx.constraint(1).accept(this);
        UnaryOperator<List<EdgeDB>> lhOp = ctx.constraint(0).accept(this);
        return edgeDBList -> {
            for (EdgeDB edgeDB : edgeDBList) {
                List<EdgeDB> lhs = lhOp.apply(List.of(edgeDB));
                List<EdgeDB> rhs = rhOp.apply(List.of(edgeDB));
                EdgeDB lhDB = EdgeDB.trueValue();
                EdgeDB rhDB = EdgeDB.trueValue();
                for (EdgeDB lh : lhs) {
                    lhDB = lhDB.and(lh);
                }
                for (EdgeDB rh : rhs) {
                    rhDB = rhDB.and(rh);
                }
                if(!lhDB.or(rhDB).isOk()) return List.of(EdgeDB.falseValue());
            }
            return List.of(EdgeDB.trueValue());
        };
    }

    @Override
    public UnaryOperator<List<EdgeDB>> visitNotConstraint(McmDslParser.NotConstraintContext ctx) {
        UnaryOperator<List<EdgeDB>> op = ctx.constraint().accept(this);
        return edgeDBList -> {
            List<EdgeDB> ret = new ArrayList<>();
            for (EdgeDB edgeDB : edgeDBList) {
                for (EdgeDB db : op.apply(List.of(edgeDB))) {
                    ret.add(db.not());
                }
            }
            return ret;
        };
    }

    @Override
    public UnaryOperator<List<EdgeDB>> visitImplyConstraint(McmDslParser.ImplyConstraintContext ctx) {
        UnaryOperator<List<EdgeDB>> rhOp = ctx.constraint(1).accept(this);
        UnaryOperator<List<EdgeDB>> lhOp = ctx.constraint(0).accept(this);
        return edgeDBList -> {
            for (EdgeDB edgeDB : edgeDBList) {
                List<EdgeDB> lhsSet = lhOp.apply(List.of(edgeDB));
                List<EdgeDB> rhsSet = rhOp.apply(List.of(edgeDB));
                EdgeDB lhs = EdgeDB.trueValue();
                EdgeDB rhs = EdgeDB.trueValue();
                for (EdgeDB db : lhsSet) {
                    lhs = lhs.and(db);
                }
                for (EdgeDB db : rhsSet) {
                    rhs = rhs.and(db);
                }
                if(lhs.isOk() && !rhs.isOk()) return List.of(EdgeDB.falseValue());
            }
            return List.of(EdgeDB.trueValue());
        };
    }

    @Override
    public UnaryOperator<List<EdgeDB>> visitSimpleConstraint(McmDslParser.SimpleConstraintContext ctx) {
        UnaryOperator<List<EdgeDB>> ret;
        currentConstraintStringSet.addAll(definitions.get(ctx.name.getText()).get2());
        if(ctx.ACYCLIC() != null) {
            ret = edgeDBList -> {
                for (EdgeDB edgeDB : edgeDBList) {
                    for (EdgeDB db : definitions.get(ctx.name.getText()).get1().apply(List.of(edgeDB))) {
                        if(!db.isAcyclic().isOk()) return List.of(EdgeDB.falseValue());
                    }
                }
                return List.of(EdgeDB.trueValue());
            };
        }
        else if(ctx.IRREFLEXIVE() != null) {
            ret = edgeDBList -> {
                for (EdgeDB edgeDB : edgeDBList) {
                    for (EdgeDB db : definitions.get(ctx.name.getText()).get1().apply(List.of(edgeDB))) {
                        if(!db.isIrreflexive().isOk()) return List.of(EdgeDB.falseValue());
                    }
                }
                return List.of(EdgeDB.trueValue());
            };
        }
        else {
            ret = edgeDBList -> {
                for (EdgeDB edgeDB : edgeDBList) {
                    for (EdgeDB db : definitions.get(ctx.name.getText()).get1().apply(List.of(edgeDB))) {
                        if(!db.isEmpty().isOk()) return List.of(EdgeDB.falseValue());
                    }
                }
                return List.of(EdgeDB.trueValue());
            };
        }

        return ret;

    }

    public MCM getMcm() {
        return mcm;
    }

}
