package hu.bme.mit.theta.analysis.algorithm.symbolic.symbolicnode.expression;

import hu.bme.mit.delta.mdd.LatticeDefinition;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.SmartBoolExprs;

import static hu.bme.mit.theta.core.type.booltype.BoolExprs.False;
import static hu.bme.mit.theta.core.type.booltype.SmartBoolExprs.And;
import static hu.bme.mit.theta.core.type.booltype.SmartBoolExprs.Not;


public class ExprLatticeDefinition {

    public static LatticeDefinition<Expr> forExpr(){
        return new LatticeDefinition<>(
                Expr.class,
                False(),
                SmartBoolExprs::Or,
                SmartBoolExprs::And,
                (a,b) -> And(a, Not(b))
        );
    }

}
