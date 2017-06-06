package hu.bme.mit.theta.core.model;

import java.util.Collection;
import java.util.Optional;

import hu.bme.mit.theta.core.Expr;
import hu.bme.mit.theta.core.Type;
import hu.bme.mit.theta.core.decl.Decl;
import hu.bme.mit.theta.core.type.booltype.BoolType;

public interface Assignment {

	Collection<? extends Decl<?>> getDecls();

	<DeclType extends Type> Optional<? extends Expr<DeclType>> eval(final Decl<DeclType> decl);

	Expr<BoolType> toExpr();
}
