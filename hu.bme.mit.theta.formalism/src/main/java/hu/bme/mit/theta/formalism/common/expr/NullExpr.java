package hu.bme.mit.theta.formalism.common.expr;

import hu.bme.mit.theta.core.expr.LitExpr;
import hu.bme.mit.theta.core.expr.NullaryExpr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.formalism.common.type.PointerType;

public interface NullExpr<T extends Type> extends NullaryExpr<PointerType<T>>, LitExpr<PointerType<T>> {
}
