package hu.bme.mit.theta.analysis.algorithm.kind;

import hu.bme.mit.theta.analysis.algorithm.SafetyChecker;
import hu.bme.mit.theta.analysis.algorithm.SafetyResult;
import hu.bme.mit.theta.analysis.expr.ExprAction;
import hu.bme.mit.theta.analysis.expr.ExprState;
import hu.bme.mit.theta.analysis.unit.UnitPrec;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;

public class KIndChecker<S  extends ExprState, A extends ExprAction> implements SafetyChecker<S, A, UnitPrec> {
    final Expr<BoolType> trans;
    final Expr<BoolType> init;
    final Expr<BoolType> prop;

    public KIndChecker(Expr<BoolType> trans, Expr<BoolType> init, Expr<BoolType> prop) {
        this.trans = trans;
        this.init = init;
        this.prop = prop;
    }

    @Override
    public SafetyResult<S, A> check(UnitPrec prec) {

        return null;
    }


}
