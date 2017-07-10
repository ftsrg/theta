package hu.bme.mit.theta.core.model;

import java.util.Collection;
import java.util.Optional;

import hu.bme.mit.theta.core.Decl;
import hu.bme.mit.theta.core.Expr;
import hu.bme.mit.theta.core.Type;

/**
 * Interface for a substitution, which is a mapping from declarations to
 * expressions.
 */
public interface Substitution {

	Collection<? extends Decl<?>> getDecls();

	<DeclType extends Type> Optional<? extends Expr<DeclType>> eval(final Decl<DeclType> decl);
}
