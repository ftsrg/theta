package hu.bme.mit.theta.analysis.algorithm.symbolic.expression;

import hu.bme.mit.theta.core.decl.Decl;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.solver.Solver;
import hu.bme.mit.theta.solver.SolverStatus;

import java.util.ArrayList;
import java.util.List;
import java.util.Optional;

import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Neq;

public class AssignmentEnumerator<T extends Type> {

    private final Expr<BoolType> expr;
    private final Decl<T> decl;

    private final List<LitExpr<T>> enumeratedAssignments;
    private boolean enumeratedAll;

    private final Solver solver;

    public AssignmentEnumerator(Expr<BoolType> expr, Decl<T> decl, Solver solver) {
        this.expr = expr;
        this.decl = decl;
        this.solver = solver;

        this.enumeratedAssignments = new ArrayList<>();
        this.enumeratedAll = false;
        solver.add(expr);
    }

    public Optional<LitExpr<T>> get(int index) {
        while(enumeratedAssignments.size() <= index && !enumeratedAll) queryNext();
        if(enumeratedAll) return Optional.empty();
        return Optional.of(enumeratedAssignments.get(index));
    }

    public boolean enumeratedAll() {
        return enumeratedAll;
    }

    private void queryNext() {
        solver.check();
        if(solver.getStatus().isSat()){
            Optional<LitExpr<T>> optionalLitExpr = solver.getModel().eval(decl);
            if(optionalLitExpr.isPresent()){
                LitExpr<T> literal = optionalLitExpr.get();
                enumeratedAssignments.add(literal);
                solver.add(Neq(decl.getRef(), literal));
                return;
            }
        }
        enumeratedAll = true;
    }
}
