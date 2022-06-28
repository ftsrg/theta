package hu.bme.mit.theta.analysis.algorithm.symbolic.symbolicnode.expression;

import com.google.common.base.Preconditions;
import com.google.common.base.Supplier;
import hu.bme.mit.delta.Pair;
import hu.bme.mit.delta.java.mdd.MddVariable;
import hu.bme.mit.theta.analysis.algorithm.symbolic.symbolicnode.MddSymbolicNode;
import hu.bme.mit.theta.analysis.algorithm.symbolic.symbolicnode.MddSymbolicNodeTraverser;
import hu.bme.mit.theta.core.decl.Decl;
import hu.bme.mit.theta.core.model.MutableValuation;
import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.type.booltype.TrueExpr;
import hu.bme.mit.theta.core.utils.ExprUtils;
import hu.bme.mit.theta.solver.Solver;
import hu.bme.mit.theta.solver.SolverStatus;
import hu.bme.mit.theta.solver.utils.WithPushPop;

import java.util.Optional;
import java.util.OptionalInt;
import java.util.Stack;

import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Eq;
import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Neq;

public class ExpressionNodeTraverser extends MddSymbolicNodeTraverser {

    private MddSymbolicNode currentNode;

    private final Solver solver;

    private final Stack<MddSymbolicNode> stack;
    private int pushedNegatedAssignments = 0;


    public ExpressionNodeTraverser(MddSymbolicNode rootNode, Supplier<Solver> solverSupplier) {
        this.solver = solverSupplier.get();
        this.stack = new Stack<>();

        this.currentNode = Preconditions.checkNotNull(rootNode);
        stack.push(rootNode);
        solver.add(((Pair<Expr<BoolType>, MddVariable>)rootNode.getSymbolicRepresentation()).first);
        pushNegatedAssignments();
    }

    @Override
    public boolean isOn(final MddSymbolicNode node){
        Preconditions.checkNotNull(node);
        return currentNode.equals(node);
    }

    @Override
    public MddSymbolicNode getCurrentNode(){
        return currentNode;
    }

    @Override
    public MddSymbolicNode moveUp(){
        Preconditions.checkState(stack.size()>1);
        popNegatedAssignments();
        solver.pop(); // pop assignment that brought us here
        currentNode = stack.pop();
        pushNegatedAssignments();
        return currentNode;
    }

    @Override
    public boolean queryNext(int assignment){
        if(currentNode.getCacheView().keySet().contains(assignment)) return true;
        else if(!currentNode.isComplete()){
            final SolverStatus status;
            final Valuation model;
            final LitExpr<?> litExpr = LitExprConverter.toLitExpr(assignment, currentNode.getVariable().getTraceInfo(Decl.class).getType());
            try(WithPushPop wpp = new WithPushPop(solver)){
                solver.add(Eq(currentNode.getVariable().getTraceInfo(Decl.class).getRef(), litExpr));
                solver.check();
                status = solver.getStatus();
                model = solver.getModel();
            }
            Preconditions.checkNotNull(status);
            if(status.isSat()) {
                cacheModel(model);
                solver.add(Neq(currentNode.getVariable().getTraceInfo(Decl.class).getRef(), litExpr));
                pushedNegatedAssignments++;
                return true;
            }
        }
        return false;
    }

    @Override
    public OptionalInt queryNext(){
        if(!currentNode.isComplete()){
            if(pushedNegatedAssignments != currentNode.getCacheView().keySet().size()){
                popNegatedAssignments();
                pushNegatedAssignments();
            }
            solver.check();
            if(solver.getStatus().isSat()){
                final Valuation model = solver.getModel();
                Optional<LitExpr<?>> optionalLitExpr = model.eval(currentNode.getVariable().getTraceInfo(Decl.class));
                if(optionalLitExpr.isPresent()){
                    LitExpr<?> literal = optionalLitExpr.get();
                    solver.add(Neq(currentNode.getVariable().getTraceInfo(Decl.class).getRef(), literal));
                    pushedNegatedAssignments++;
                    cacheModel(model);
                    return OptionalInt.of(LitExprConverter.toInt(literal));
                } else {
                    // TODO na itt mi van?
                    throw new UnsupportedOperationException("Not implemented yet");
                }
            } else {
                setComplete(currentNode);
            }
        }
        return OptionalInt.empty();
    }

    // TODO összevonni queryChilddal
    public MddSymbolicNode moveDown(int assignment){
        if(queryNext(assignment)){
            popNegatedAssignments();
            solver.push();
            solver.add(Eq(currentNode.getVariable().getTraceInfo(Decl.class).getRef(), LitExprConverter.toLitExpr(assignment, currentNode.getVariable().getTraceInfo(Decl.class).getType())));
            currentNode = currentNode.getCacheView().get(assignment);
            stack.push(currentNode);
            pushNegatedAssignments();
            return currentNode;
        } else return null;
    }

    private void pushNegatedAssignments(){
        solver.push();
        for(var cur = currentNode.getCacheView().cursor();cur.moveNext();){
            solver.add(Neq(currentNode.getVariable().getTraceInfo(Decl.class).getRef(), LitExprConverter.toLitExpr(cur.key(), currentNode.getVariable().getTraceInfo(Decl.class).getType())));
            pushedNegatedAssignments++;
        }
    }

    private void popNegatedAssignments(){
        solver.pop();
        pushedNegatedAssignments = 0;
    }

    private void cacheModel(Valuation valuation){
        MddSymbolicNode node = currentNode;
        Expr expr = ((Pair<Expr<BoolType>, MddVariable>)node.getSymbolicRepresentation()).first;
        MddVariable variable = node.getVariable();

        while(variable != null){

            final Optional<? extends MddVariable> lower = variable.getLower();
            final Decl decl = variable.getTraceInfo(Decl.class);
            final Optional<LitExpr<?>> literal = valuation.eval(decl);

            if(literal.isPresent()){
                final MutableValuation val = new MutableValuation();

                val.put(decl, literal.get());
                expr = ExprUtils.simplify(expr, val);

                if(lower.isPresent()){
                    MddSymbolicNode childNode;
                    if(node.getCacheView().containsKey(LitExprConverter.toInt(literal.get()))){
                        // Existing cached child
                        childNode = node.getCacheView().get(LitExprConverter.toInt(literal.get()));
                        assert childNode.isOn(lower.get());
                    } else {
                        // New child
                        // TODO hashcode
                        childNode = ExpressionNodeUtils.uniqueTable.checkIn(new MddSymbolicNode(new Pair<>((Expr<BoolType>) expr,lower.get()),lower.get().getLevel()));
                        cacheNode(node,LitExprConverter.toInt(literal.get()),childNode);
                    }
                    node = childNode;
                    variable = lower.get();

                } else {
                    if(expr instanceof TrueExpr){
                        setComplete(ExpressionNodeUtils.terminalOne);
                        cacheNode(node,LitExprConverter.toInt(literal.get()), ExpressionNodeUtils.terminalOne);
                    } else {
                        cacheNode(node,LitExprConverter.toInt(literal.get()),null);
                    }
                    // TODO itt mi van?
                    variable = null;
                }


            } else {
                // TODO ilyenkor bármi lehet az értéke
                // máshogy kell kezelni ha azért mert nincs benne a kifejezésben, meg ha azért mert minden behelyettesítésére igaz
            }
        }
    }


}
