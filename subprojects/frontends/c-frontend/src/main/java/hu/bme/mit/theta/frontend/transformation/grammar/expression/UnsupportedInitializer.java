package hu.bme.mit.theta.frontend.transformation.grammar.expression;

import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.core.type.NullaryExpr;
import hu.bme.mit.theta.core.type.inttype.IntType;

import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;

public class UnsupportedInitializer extends NullaryExpr<IntType> {

    @Override
    public IntType getType() {
        return Int();
    }

    @Override
    public LitExpr<IntType> eval(Valuation val) {
        throw new UnsupportedOperationException("UnsupportedInitializer expressions are not supported.");
    }

    @Override
    public String toString() {
        return "UnsupportedInitializer";
    }
}
