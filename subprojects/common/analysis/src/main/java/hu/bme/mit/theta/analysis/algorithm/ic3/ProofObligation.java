package hu.bme.mit.theta.analysis.algorithm.ic3;

import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;

import java.util.Set;

public class ProofObligation {
    private Set<Expr<BoolType>> expressions;
    private int time;
    ProofObligation(Set<Expr<BoolType>> expressions, int time){
        this.expressions = expressions;
        this.time = time;
    }

    public int getTime() {
        return time;
    }

    public Set<Expr<BoolType>> getExpressions() {
        return expressions;
    }
}
