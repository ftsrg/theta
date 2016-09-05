package hu.bme.mit.inf.theta.formalism.common.expr;

import hu.bme.mit.inf.theta.core.expr.LitExpr;
import hu.bme.mit.inf.theta.core.expr.NullaryExpr;
import hu.bme.mit.inf.theta.core.type.Type;
import hu.bme.mit.inf.theta.formalism.common.type.PointerType;

public interface NullExpr<T extends Type> extends NullaryExpr<PointerType<T>>, LitExpr<PointerType<T>> {
}
