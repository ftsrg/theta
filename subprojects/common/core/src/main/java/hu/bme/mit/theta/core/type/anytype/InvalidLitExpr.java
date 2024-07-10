package hu.bme.mit.theta.core.type.anytype;

import com.google.common.base.Preconditions;
import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.core.type.NullaryExpr;
import hu.bme.mit.theta.core.type.Type;

public class InvalidLitExpr<ExprType extends Type> extends NullaryExpr<ExprType> implements LitExpr<ExprType> {

    private final ExprType type;

    public InvalidLitExpr(ExprType type) {
        this.type = Preconditions.checkNotNull(type);
    }

    @Override
    public ExprType getType() {
        return type;
    }

    @Override
    public LitExpr<ExprType> eval(Valuation val) {
        return this;
    }

    @Override
    public boolean isInvalid() {
        return true;
    }

    @Override
    public boolean equals(Object obj) {
        return false;
    }
}
