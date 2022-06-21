package hu.bme.mit.theta.analysis.algorithm.symbolic.expression;

import com.google.common.base.Preconditions;
import com.google.common.base.Supplier;
import com.koloboke.collect.set.ObjSet;
import com.koloboke.collect.set.hash.HashObjSets;
import hu.bme.mit.theta.core.decl.Decl;
import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.solver.Solver;
import hu.bme.mit.theta.solver.SolverStatus;
import hu.bme.mit.theta.solver.utils.WithPushPop;

import java.util.Optional;
import java.util.Stack;

import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Eq;
import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Neq;

public class ExpressionNodeTraverser {

    private NodeEnumeration currentEnumeration;

    private final Solver solver;
    private final Stack<NodeEnumeration> stack;

    private class NodeEnumeration{
        private final ExpressionNode node;
        private final ObjSet<LitExpr<?>> enumeratedAssignments;

        private NodeEnumeration(ExpressionNode node) {
            this.node = node;
            this.enumeratedAssignments = HashObjSets.newMutableSet();
        }
    }

    public ExpressionNodeTraverser(ExpressionNode rootNode, Supplier<Solver> solverSupplier) {
        this.solver = solverSupplier.get();
        this.stack = new Stack<>();

        this.currentEnumeration = new NodeEnumeration(Preconditions.checkNotNull(rootNode));
        solver.add(rootNode.getSymbolicRepresentation(Expr.class));
    }

    public boolean isOn(final ExpressionNode node){
        Preconditions.checkNotNull(node);
        return currentEnumeration.node.equals(node);
    }

    public void moveUp(){
        solver.pop(currentEnumeration.enumeratedAssignments.size()); // pop for each horizontal push
        solver.pop(); // pop for vertical push
        currentEnumeration = stack.pop();
    }

    public boolean queryAssignment(LitExpr<?> assignment){
        if(currentEnumeration.enumeratedAssignments.contains(assignment)) return true; // TODO inkább a node cache-ét kéne nézni (vagy azt is)
        else if(!currentEnumeration.node.isComplete()){
            SolverStatus status;
            try(WithPushPop wpp = new WithPushPop(solver)){
                solver.add(Eq(currentEnumeration.node.getVariable().getTraceInfo(Decl.class).getRef(),assignment));
                solver.check();
                status = solver.getStatus();
            }
            Preconditions.checkNotNull(status);
            if(status.isSat()) {
                currentEnumeration.enumeratedAssignments.add(assignment);
                solver.add(Neq(currentEnumeration.node.getVariable().getTraceInfo(Decl.class).getRef(), assignment));
                cacheModel(solver.getModel());
                return true;
            }
        }
        return false;
    }

    public void queryAssignment(){
        if(!currentEnumeration.node.isComplete()){
            solver.check();
            if(solver.getStatus().isSat()){
                Optional<LitExpr<?>> optionalLitExpr = solver.getModel().eval(currentEnumeration.node.getVariable().getTraceInfo(Decl.class));
                if(optionalLitExpr.isPresent()){
                    LitExpr<?> literal = optionalLitExpr.get();
                    currentEnumeration.enumeratedAssignments.add(literal);
                    solver.add(Neq(currentEnumeration.node.getVariable().getTraceInfo(Decl.class).getRef(), literal));

                    cacheModel(solver.getModel());
                } else {
                    // TODO na itt mi van?
                }
            } else {
                currentEnumeration.node.setComplete();
            }
        }

    }

    public void moveDown(LitExpr<?> assignment){

    }

    private void cacheModel(Valuation model){
        // végigsimplifyolgatni
        // unique tableből lekéregetni az expression node-okat
        // csak a var orderingben lévő változók értékeit elrakosgatni és csak abban a sorrendben
        ExpressionNodeUtils.cacheModel(currentEnumeration.node,model);
    }


}
