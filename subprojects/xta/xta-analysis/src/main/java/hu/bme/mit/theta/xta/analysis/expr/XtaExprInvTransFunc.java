package hu.bme.mit.theta.xta.analysis.expr;

import com.google.common.collect.ImmutableList;
import hu.bme.mit.theta.analysis.InvTransFunc;
import hu.bme.mit.theta.analysis.expr.BasicExprState;
import hu.bme.mit.theta.analysis.unit.UnitPrec;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.xta.analysis.XtaAction;
import hu.bme.mit.theta.xta.analysis.expl.XtaExplUtils;

import java.util.Collection;

public final class XtaExprInvTransFunc implements InvTransFunc<BasicExprState, XtaAction, UnitPrec> {

    private final static XtaExprInvTransFunc INSTANCE = new XtaExprInvTransFunc();

    private XtaExprInvTransFunc() {
    }

    public static XtaExprInvTransFunc getInstance() {
        return INSTANCE;
    }

    @Override
    public Collection<? extends BasicExprState> getPreStates(BasicExprState state, XtaAction action, UnitPrec prec) {
        final Expr<BoolType> preExpr = XtaExplUtils.pre(state.toExpr(), action);
        return ImmutableList.of(BasicExprState.of(preExpr));
    }
}
