package hu.bme.mit.theta.xcfa.analysis.impl.lazy;

import hu.bme.mit.theta.analysis.expr.BasicExprState;
import hu.bme.mit.theta.analysis.algorithm.lazy.expr.ExprActionPost;
import hu.bme.mit.theta.xcfa.analysis.common.XcfaAction;

public class XcfaExprActionPost implements ExprActionPost<XcfaAction> {
    private final QuantifiedExprActionPost<XcfaAction> exprActionPost = new QuantifiedExprActionPost<>();
    private XcfaExprActionPost() {}

    public static XcfaExprActionPost create() {
        return new XcfaExprActionPost();
    }

    @Override
    public BasicExprState post(BasicExprState state, XcfaAction action) {
        return exprActionPost.post(state, action);
    }
}
