package hu.bme.mit.theta.xcfa.analysis.impl.lazy;

import com.google.common.collect.Lists;
import hu.bme.mit.theta.analysis.algorithm.lazy.expr.ExprActionPre;
import hu.bme.mit.theta.core.stmt.Stmt;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.utils.WpState;
import hu.bme.mit.theta.xcfa.analysis.common.XcfaAction;

public class XcfaExprActionPre implements ExprActionPre<XcfaAction> {
    private XcfaExprActionPre() {}

    public static XcfaExprActionPre create() {
        return new XcfaExprActionPre();
    }

    @Override
    public Expr<BoolType> pre(Expr<BoolType> state, XcfaAction action) {
        WpState wp = WpState.of(state);
        for(final Stmt stmt : Lists.reverse(action.getStmts())) {
            wp = wp.wep(stmt);
        }
        return wp.getExpr();
    }
}
