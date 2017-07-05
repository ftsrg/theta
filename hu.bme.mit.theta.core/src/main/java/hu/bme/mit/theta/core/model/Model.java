
package hu.bme.mit.theta.core.model;

import java.util.Collection;
import java.util.Optional;

import hu.bme.mit.theta.core.Decl;
import hu.bme.mit.theta.core.LitExpr;
import hu.bme.mit.theta.core.Type;
import hu.bme.mit.theta.core.decl.ConstDecl;

/**
 * Interface for a model, which is a special type of assignment, mapping
 * constant declarations to literal expressions.
 */
public interface Model extends Substitution {

	@Override
	Collection<? extends ConstDecl<?>> getDecls();

	@Override
	<DeclType extends Type> Optional<LitExpr<DeclType>> eval(final Decl<DeclType> decl);

}
