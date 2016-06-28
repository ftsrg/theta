package hu.bme.mit.inf.ttmc.formalism.common.expr;

import hu.bme.mit.inf.ttmc.core.expr.LitExpr;
import hu.bme.mit.inf.ttmc.core.expr.NullaryExpr;
import hu.bme.mit.inf.ttmc.core.type.Type;
import hu.bme.mit.inf.ttmc.formalism.common.type.PointerType;

public interface NullExpr<T extends Type> extends NullaryExpr<PointerType<T>>, LitExpr<PointerType<T>> {
}
