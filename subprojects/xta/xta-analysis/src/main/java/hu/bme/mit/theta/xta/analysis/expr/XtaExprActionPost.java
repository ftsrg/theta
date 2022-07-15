package hu.bme.mit.theta.xta.analysis.expr;

import hu.bme.mit.theta.analysis.algorithm.lazy.expr.ExprActionPost;
import hu.bme.mit.theta.analysis.expr.BasicExprState;
import hu.bme.mit.theta.xta.analysis.XtaAction;
import hu.bme.mit.theta.xta.analysis.XtaDataAction;

public class XtaExprActionPost implements ExprActionPost<XtaAction> {
    private final QuantifiedExprActionPost<XtaDataAction> exprActionPost = new QuantifiedExprActionPost<>();
    private XtaExprActionPost() {}

    public static XtaExprActionPost create() {
        return new XtaExprActionPost();
    }

    @Override
    public BasicExprState post(BasicExprState state, XtaAction action) {
        return exprActionPost.post(state, XtaDataAction.of(action));
    }
}
