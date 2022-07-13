package hu.bme.mit.theta.analysis.algorithm.symbolic.symbolicnode.expression;

import com.google.common.base.Preconditions;
import hu.bme.mit.delta.Pair;
import hu.bme.mit.delta.collections.IntSetView;
import hu.bme.mit.delta.java.mdd.MddVariable;
import hu.bme.mit.theta.analysis.algorithm.symbolic.symbolicnode.MddSymbolicNode;
import hu.bme.mit.theta.analysis.algorithm.symbolic.symbolicnode.MddSymbolicNodeTraverser;
import hu.bme.mit.theta.core.decl.ConstDecl;
import hu.bme.mit.theta.core.model.MutableValuation;
import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.core.utils.ExprUtils;
import hu.bme.mit.theta.solver.Solver;
import hu.bme.mit.theta.solver.SolverStatus;
import hu.bme.mit.theta.solver.utils.WithPushPop;

import java.util.Optional;
import java.util.Stack;
import java.util.function.Supplier;

import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Eq;
import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Neq;

public class ExprNodeTraverser implements MddSymbolicNodeTraverser {

    private MddSymbolicNode currentNode;

    private final Solver solver;

    private final Stack<MddSymbolicNode> stack;
    private int pushedNegatedAssignments = 0;


    public ExprNodeTraverser(MddSymbolicNode rootNode, Supplier<Solver> solverSupplier) {
        this.solver = solverSupplier.get();
        this.stack = new Stack<>();

        setCurrentNode(Preconditions.checkNotNull(rootNode));
        solver.add(rootNode.getSymbolicRepresentation(Expr.class).first);
        solver.push();
    }

    @Override
    public MddSymbolicNode getCurrentNode(){
        return currentNode;
    }

    @Override
    public MddSymbolicNode moveUp(){
        Preconditions.checkState(stack.size()>0);
        popNegatedAssignments();
        solver.pop(); // pop assignment that brought us here
        setCurrentNode(stack.pop());
        return currentNode;
    }

    @Override
    public boolean queryEdge(int assignment){
        if(currentNode.getCacheView().keySet().contains(assignment) || currentNode.getCacheView().defaultValue() != null) return true;
        else if(!currentNode.isComplete()){
            final SolverStatus status;
            final Valuation model;
            final LitExpr<?> litExpr = LitExprConverter.toLitExpr(assignment, currentNode.getSymbolicRepresentation().second.getTraceInfo(ConstDecl.class).getType());
            try(WithPushPop wpp = new WithPushPop(solver)){
                solver.add(Eq(currentNode.getSymbolicRepresentation().second.getTraceInfo(ConstDecl.class).getRef(), litExpr));
                solver.check();
                status = solver.getStatus();
                model = status.isSat() ? solver.getModel() : null;
            }
            Preconditions.checkNotNull(status);
            if(status.isSat()) {
                cacheModel(model);
                solver.add(Neq(currentNode.getSymbolicRepresentation().second.getTraceInfo(ConstDecl.class).getRef(), litExpr));
                pushedNegatedAssignments++;
                return true;
            }
        }
        return false;
    }

    @Override
    public MddSymbolicNode peakDown(int assignment) {
        queryEdge(assignment);
        return currentNode.getCacheView().get(assignment);
    }

    @Override
    public QueryResult queryEdge(){
        if(!currentNode.isComplete()){
            if(pushedNegatedAssignments != currentNode.getCacheView().keySet().size()){
                popNegatedAssignments();
                pushNegatedAssignments();
            }
            solver.check();
            if(solver.getStatus().isSat()){
                final Valuation model = solver.getModel();
                final ConstDecl<?> decl = currentNode.getSymbolicRepresentation().second.getTraceInfo(ConstDecl.class);
                final Optional<? extends LitExpr<?>> optionalLitExpr = model.eval(decl);

                final LitExpr<?> literal;
                final Valuation modelToCache;
                if(optionalLitExpr.isPresent()) {
                    literal = optionalLitExpr.get();
                    modelToCache = model;
                } else {
                    final int newValue;
                    if (currentNode.getSymbolicRepresentation().second.isBounded()) {
                        final IntSetView domain = IntSetView.range(0, currentNode.getSymbolicRepresentation().second.getDomainSize());
                        final IntSetView remaining = domain.minus(currentNode.getCacheView().keySet());
                        if (remaining.isEmpty()) {
                            currentNode.getExplicitRepresentation().setComplete();
                            return new QueryResult(QueryResult.Status.FAILED);
                        } else {
                            final var cur = remaining.cursor();
                            Preconditions.checkState(cur.moveNext());
                            newValue = cur.elem();
                        }
                    } else {
                        final IntSetView cachedKeys = currentNode.getCacheView().keySet();
                        newValue = cachedKeys.isEmpty() ? 0 : cachedKeys.statistics().highestValue() + 1;
                    }
                    literal = LitExprConverter.toLitExpr(newValue, decl.getType());
                    final var extendedModel = MutableValuation.copyOf(model);
                    extendedModel.put(decl, literal);
                    modelToCache = extendedModel;
                }

                solver.add(Neq(decl.getRef(), literal));
                pushedNegatedAssignments++;
                cacheModel(modelToCache);
                return new QueryResult(LitExprConverter.toInt(literal));
            } else {
                currentNode.getExplicitRepresentation().setComplete();
            }
        }
        return new QueryResult(QueryResult.Status.FAILED);
    }

    // TODO összevonni queryChilddal
    public MddSymbolicNode moveDown(int assignment){
        if(queryEdge(assignment)){
            popNegatedAssignments();
            solver.push();
            solver.add(Eq(currentNode.getSymbolicRepresentation().second.getTraceInfo(ConstDecl.class).getRef(), LitExprConverter.toLitExpr(assignment, currentNode.getSymbolicRepresentation().second.getTraceInfo(ConstDecl.class).getType())));
            stack.push(currentNode);
            setCurrentNode(currentNode.getCacheView().get(assignment));
            return currentNode;
        } else return null;
    }

    private void pushNegatedAssignments(){
        solver.push();
        for(var cur = currentNode.getCacheView().cursor();cur.moveNext();){
            solver.add(Neq(currentNode.getSymbolicRepresentation().second.getTraceInfo(ConstDecl.class).getRef(), LitExprConverter.toLitExpr(cur.key(), currentNode.getSymbolicRepresentation().second.getTraceInfo(ConstDecl.class).getType())));
            pushedNegatedAssignments++;
        }
    }

    private void popNegatedAssignments(){
        solver.pop();
        pushedNegatedAssignments = 0;
    }

    private void cacheModel(Valuation valuation){
        MddSymbolicNode node = currentNode;
        Expr<?> expr = node.getSymbolicRepresentation(Expr.class).first;
        MddVariable variable = node.getSymbolicRepresentation().second;

        while(variable != null){

            final Optional<? extends MddVariable> lower = variable.getLower();
            final ConstDecl<?> decl = variable.getTraceInfo(ConstDecl.class);
            final Optional<? extends LitExpr<?>> literal = valuation.eval(decl);

            final MddSymbolicNode childNode;
            if(node.getCacheView().defaultValue() != null) {
                childNode = node.getCacheView().defaultValue();
            } else {
                final LitExpr<?> literalToCache;
                if(literal.isPresent()){
                    literalToCache = literal.get();
                } else {
                    final int newValue;
                    if (node.getSymbolicRepresentation().second.isBounded()) {
                        final IntSetView domain = IntSetView.range(0, node.getSymbolicRepresentation().second.getDomainSize());
                        final IntSetView remaining = domain.minus(node.getCacheView().keySet());
                        if (remaining.isEmpty()) {
                            node.getExplicitRepresentation().setComplete();
                            return;
                        } else {
                            final var cur = remaining.cursor();
                            Preconditions.checkState(cur.moveNext());
                            newValue = cur.elem();
                        }
                    } else {
                        final IntSetView cachedKeys = node.getCacheView().keySet();
                        newValue = cachedKeys.isEmpty() ? 0 : cachedKeys.statistics().highestValue() + 1;
                    }
                    literalToCache = LitExprConverter.toLitExpr(newValue, decl.getType());
                }

                final MutableValuation val = new MutableValuation();
                val.put(decl, literalToCache);
                expr = ExprUtils.simplify(expr, val);

                if(node.getCacheView().containsKey(LitExprConverter.toInt(literalToCache))){
                    childNode = node.getCacheView().get(LitExprConverter.toInt(literalToCache));
                    assert lower.isEmpty() || childNode.isOn(lower.get());
                } else {

                    // TODO a getLevel DdLevel<MddNode>-ot ad és a symbolic node még nem az
//                        final DdLevel<MddSymbolicNode> level = node.getSymbolicRepresentation().second.getLevel();
//                        final MddSymbolicNode.SymbolicRepresentation symbolicRepresentation = MddSymbolicNode.SymbolicRepresentation.of(new Pair<>((Expr<BoolType>) expr,lower.get()));
//                        childNode = level.checkIn(symbolicRepresentation, sr -> new MddSymbolicNode((MddSymbolicNode.SymbolicRepresentation) sr));

                    childNode = ExprNodeUtils.uniqueTable.checkIn(new MddSymbolicNode(new Pair<>(expr,lower.orElse(null))));
                    node.getExplicitRepresentation().cacheNode(LitExprConverter.toInt(literalToCache),childNode);
                }
            }

            node = childNode;
            variable = lower.orElse(null);
        }
    }

    private void setCurrentNode(MddSymbolicNode node){
        this.currentNode = node;
        pushNegatedAssignments();
        if(!node.isTerminal() || !node.isComplete()) checkIfDefault();
    }

    private void checkIfDefault(){
        final Expr<?> expr = currentNode.getSymbolicRepresentation(Expr.class).first;
        if(!ExprUtils.getConstants(expr).contains(currentNode.getSymbolicRepresentation().second.getTraceInfo(ConstDecl.class))){
            final MddSymbolicNode childNode = ExprNodeUtils.uniqueTable.checkIn(new MddSymbolicNode(new Pair<>(expr,currentNode.getSymbolicRepresentation().second.getLower().orElse(null))));
            if(currentNode.getCacheView().defaultValue() != null) Preconditions.checkState(currentNode.getCacheView().defaultValue().equals(childNode));
            else {
                currentNode.getExplicitRepresentation().cacheDefault(childNode);
                currentNode.getExplicitRepresentation().setComplete();
            }
        }
    }
}
