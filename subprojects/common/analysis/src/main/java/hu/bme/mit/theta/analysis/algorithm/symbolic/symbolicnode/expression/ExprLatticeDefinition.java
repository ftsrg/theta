package hu.bme.mit.theta.analysis.algorithm.symbolic.symbolicnode.expression;

import hu.bme.mit.delta.mdd.LatticeDefinition;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolExprs;

import static hu.bme.mit.theta.core.type.booltype.BoolExprs.*;

public class ExprLatticeDefinition {

    public static LatticeDefinition<Expr> forExpr(){
        return new LatticeDefinition<>(
                Expr.class,
                False(),
                BoolExprs::Or,
                BoolExprs::And,
                (a,b) -> And(a, Not(b))
        );
    }

}
