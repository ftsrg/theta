package hu.bme.mit.theta.xta.analysis.expr;

import hu.bme.mit.theta.analysis.algorithm.lazy.expr.ExprPost;
import hu.bme.mit.theta.analysis.expr.BasicExprState;
import hu.bme.mit.theta.xta.analysis.XtaAction;
import hu.bme.mit.theta.xta.analysis.XtaDataAction;

public class XtaExprPost implements ExprPost<XtaAction> {
    private final QuantifiedExprPost<XtaDataAction> exprActionPost = new QuantifiedExprPost<>();
    private XtaExprPost() {}

    public static XtaExprPost create() {
        return new XtaExprPost();
    }

    @Override
    public BasicExprState post(BasicExprState state, XtaAction action) {
        return exprActionPost.post(state, XtaDataAction.of(action));
    }
}
