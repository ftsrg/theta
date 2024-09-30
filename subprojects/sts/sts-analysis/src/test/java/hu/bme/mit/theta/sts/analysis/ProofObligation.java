package hu.bme.mit.theta.sts.analysis;

import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;

import java.util.Collection;

public class ProofObligation {
    private Collection<Expr<BoolType>> expressions;
    private int time;
    ProofObligation(Collection<Expr<BoolType>> expressions, int time){
        this.expressions = expressions;
        this.time = time;
    }

    public int getTime() {
        return time;
    }

    public Collection<Expr<BoolType>> getExpressions() {
        return expressions;
    }
}
