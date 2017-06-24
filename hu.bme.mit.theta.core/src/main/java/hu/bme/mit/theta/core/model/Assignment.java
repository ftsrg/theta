package hu.bme.mit.theta.core.model;

import java.util.Collection;
import java.util.Optional;

import hu.bme.mit.theta.core.Decl;
import hu.bme.mit.theta.core.Expr;
import hu.bme.mit.theta.core.Type;
import hu.bme.mit.theta.core.type.booltype.BoolType;

/**
 * Interface for an assignment, which is a mapping from declarations to
 * expressions.
 */
public interface Assignment {

	Collection<? extends Decl<?>> getDecls();

	<DeclType extends Type> Optional<? extends Expr<DeclType>> eval(final Decl<DeclType> decl);

	Expr<BoolType> toExpr();
}
