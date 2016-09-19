package hu.bme.mit.theta.core.model;

import java.util.Collection;
import java.util.Optional;

import hu.bme.mit.theta.core.decl.Decl;
import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.type.BoolType;
import hu.bme.mit.theta.core.type.Type;

public interface Assignment {

	Collection<? extends Decl<?>> getDecls();

	<DeclType extends Type> Optional<? extends Expr<DeclType>> eval(final Decl<DeclType> decl);

	public Expr<? extends BoolType> toExpr();
}
