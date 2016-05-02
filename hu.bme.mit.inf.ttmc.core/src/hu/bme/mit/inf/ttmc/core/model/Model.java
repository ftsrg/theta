
package hu.bme.mit.inf.ttmc.core.model;

import java.util.Collection;
import java.util.Optional;

import hu.bme.mit.inf.ttmc.core.decl.ConstDecl;
import hu.bme.mit.inf.ttmc.core.expr.Expr;
import hu.bme.mit.inf.ttmc.core.type.BoolType;
import hu.bme.mit.inf.ttmc.core.type.Type;

public interface Model {

	public Collection<? extends ConstDecl<?>> getConstDecls();

	public <T extends Type> Optional<Expr<T>> eval(final ConstDecl<T> decl);

	public <T extends Type> Optional<Expr<T>> eval(final Expr<T> expr);

	public Expr<? extends BoolType> toExpr();

}
