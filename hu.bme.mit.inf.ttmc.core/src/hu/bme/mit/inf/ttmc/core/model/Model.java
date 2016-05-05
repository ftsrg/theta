
package hu.bme.mit.inf.ttmc.core.model;

import java.util.Optional;

import hu.bme.mit.inf.ttmc.core.expr.Expr;
import hu.bme.mit.inf.ttmc.core.expr.LitExpr;
import hu.bme.mit.inf.ttmc.core.type.BoolType;
import hu.bme.mit.inf.ttmc.core.type.Type;

public interface Model extends Assignment {

	public <T extends Type> Optional<LitExpr<T>> eval(final Expr<T> expr);

	public Expr<? extends BoolType> toExpr();

}
